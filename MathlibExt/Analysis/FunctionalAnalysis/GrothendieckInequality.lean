/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped InnerProductSpace

section
namespace MathlibExt.Analysis.FunctionalAnalysis.GrothendieckInequalityWanted

/-- Rademacher sign: 1 if `ω k` is true, -1 otherwise. -/
private noncomputable def radSign {d : ℕ} (k : Fin d) (ω : Fin d → Bool) : ℝ :=
  if ω k then 1 else -1

/-- Flip coordinate `k` of `ω`. -/
private def flipAt {d : ℕ} (k : Fin d) (ω : Fin d → Bool) : Fin d → Bool :=
  Function.update ω k (!(ω k))

/-- Truncation at level `M`. -/
private noncomputable def truncAt (M t : ℝ) : ℝ :=
  if |t| ≤ M then t else 0

/-- Random-sign embedding of a Euclidean vector. -/
private noncomputable def radEmbed {d : ℕ} (X : EuclideanSpace ℝ (Fin d))
    (ω : Fin d → Bool) : ℝ :=
  ∑ k, radSign k ω * X k

-- N5
private theorem truncAt_facts {M t : ℝ} (hM : 0 < M) :
    |truncAt M t| ≤ M ∧ (truncAt M t)^2 ≤ t^2 ∧ (t - truncAt M t)^2 * M^2 ≤ t^4 := by
  unfold truncAt
  by_cases h : |t| ≤ M
  · rw [ite_eq_left h]
    refine ⟨h, le_refl _, ?_⟩
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    positivity
  · rw [ite_eq_right h]
    have hlt : M < |t| := lt_of_not_ge h
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_zero]; exact le_of_lt hM
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg t
    · simp only [sub_zero]
      have hM2 : M^2 ≤ t^2 := by
        have h1 : M ≤ |t| := le_of_lt hlt
        calc M^2 ≤ |t|^2 := by
              apply sq_le_sq.mpr
              rw [abs_of_pos hM, abs_abs]
              exact h1
          _ = t^2 := sq_abs t
      have ht2 : 0 ≤ t^2 := sq_nonneg t
      calc t^2 * M^2 ≤ t^2 * t^2 := by
            apply mul_le_mul_of_nonneg_left hM2 ht2
        _ = t^4 := by ring

-- N2 helpers
private theorem flipAt_involutive {d : ℕ} (k : Fin d) : Function.Involutive (flipAt k) := by
  intro ω
  simp [flipAt]

private theorem radSign_flip_self {d : ℕ} (k : Fin d) (ω : Fin d → Bool) :
    radSign k (flipAt k ω) = -radSign k ω := by
  simp [radSign, flipAt, Function.update_self]
  by_cases h : ω k <;> simp [h]

private theorem radSign_flip_ne {d : ℕ} {k l : Fin d} (hkl : l ≠ k) (ω : Fin d → Bool) :
    radSign l (flipAt k ω) = radSign l ω := by
  simp [radSign, flipAt, Function.update_of_ne hkl]

private theorem radSign_sq {d : ℕ} (k : Fin d) (ω : Fin d → Bool) :
    radSign k ω * radSign k ω = 1 := by
  simp [radSign]
  by_cases h : ω k <;> simp [h]

-- N2
private theorem radSign_flip_sum_eq_zero {d : ℕ} (k : Fin d)
    (f : (Fin d → Bool) → ℝ) (hf : ∀ ω, f (flipAt k ω) = f ω) :
    ∑ ω, f ω * radSign k ω = 0 := by
  have hperm : ∀ ω, f (flipAt k ω) * radSign k (flipAt k ω) = -(f ω * radSign k ω) := by
    intro ω
    rw [hf ω, radSign_flip_self k ω]
    ring
  have hS : ∑ ω, f (flipAt k ω) * radSign k (flipAt k ω) = ∑ ω, f ω * radSign k ω := by
    have h := Equiv.sum_comp ((flipAt_involutive k).toPerm) (fun ω => f ω * radSign k ω)
    simpa [Function.Involutive.toPerm] using h
  have hneg : ∑ ω, f (flipAt k ω) * radSign k (flipAt k ω) = -(∑ ω, f ω * radSign k ω) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun ω _ => hperm ω)
  linarith

-- N1 (part2)
private theorem abs_bilinear_le_sq_mul_of_sign_bound
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {M β : ℝ} (hM : 0 ≤ M)
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ M) (hb : ∀ j, |b j| ≤ M) :
    |∑ i : Fin m, ∑ j : Fin n, A i j * a i * b j| ≤ M^2 * β := by
  set c : Fin m → ℝ := fun i => ∑ j, A i j * b j with hc
  set ε : Fin m → ℝ := fun i => if 0 ≤ c i then 1 else -1 with hε
  have hεsign : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    simp only [hε]
    by_cases h : 0 ≤ c i <;> simp [h]
  have hεc : ∀ i, ε i * c i = |c i| := by
    intro i
    simp only [hε]
    by_cases h : 0 ≤ c i
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hS : (∑ i : Fin m, ∑ j : Fin n, A i j * a i * b j) = ∑ i, a i * c i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  set d : Fin n → ℝ := fun j => ∑ i, A i j * ε i with hd
  set δ : Fin n → ℝ := fun j => if 0 ≤ d j then 1 else -1 with hδ
  have hδsign : ∀ j, δ j = 1 ∨ δ j = -1 := by
    intro j
    simp only [hδ]
    by_cases h : 0 ≤ d j <;> simp [h]
  have hδd : ∀ j, δ j * d j = |d j| := by
    intro j
    simp only [hδ]
    by_cases h : 0 ≤ d j
    · rw [ite_eq_left h, one_mul, abs_of_nonneg h]
    · rw [ite_eq_right h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hT : (∑ i, ε i * c i) = ∑ j, d j * b j := by
    have e1 : (∑ i, ε i * c i) = ∑ i, ∑ j, ε i * (A i j * b j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, Finset.mul_sum]
    have e2 : (∑ i, ∑ j, ε i * (A i j * b j)) = ∑ j, ∑ i, ε i * (A i j * b j) :=
      Finset.sum_comm
    have e3 : (∑ j, ∑ i, ε i * (A i j * b j)) = ∑ j, d j * b j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hd]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e1, e2, e3]
  have hU : (∑ j, δ j * d j) = ∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j := by
    simp only [hd]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hUbound : |∑ j, δ j * d j| ≤ β := by
    rw [hU]
    exact hsign ε δ hεsign hδsign
  have hST : |∑ i, a i * c i| ≤ M * |∑ i, ε i * c i| := by
    have h1 : |∑ i, a i * c i| ≤ ∑ i, M * |c i| := by
      calc |∑ i, a i * c i| ≤ ∑ i, |a i * c i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |a i| * |c i| := by
              apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
        _ ≤ ∑ i, M * |c i| := by
              apply Finset.sum_le_sum
              intro i _
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact ha i
    have heq : (∑ i, ε i * c i) = ∑ i, |c i| :=
      Finset.sum_congr rfl (fun i _ => hεc i)
    have h2 : (∑ i, M * |c i|) = M * |∑ i, ε i * c i| := by
      rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)),
        Finset.mul_sum]
    rwa [h2] at h1
  have hTU : |∑ j, d j * b j| ≤ M * |∑ j, δ j * d j| := by
    have h1 : |∑ j, d j * b j| ≤ ∑ j, M * |d j| := by
      calc |∑ j, d j * b j| ≤ ∑ j, |d j * b j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |d j| * |b j| := by
              apply Finset.sum_congr rfl; intro j _; rw [abs_mul]
        _ ≤ ∑ j, |d j| * M := by
              apply Finset.sum_le_sum
              intro j _
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact hb j
        _ = ∑ j, M * |d j| := by
              apply Finset.sum_congr rfl; intro j _; ring
    have heq : (∑ j, δ j * d j) = ∑ j, |d j| :=
      Finset.sum_congr rfl (fun j _ => hδd j)
    have h2 : (∑ j, M * |d j|) = M * |∑ j, δ j * d j| := by
      rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)),
        Finset.mul_sum]
    rwa [h2] at h1
  rw [hS]
  calc |∑ i, a i * c i| ≤ M * |∑ i, ε i * c i| := hST
    _ = M * |∑ j, d j * b j| := by rw [hT]
    _ ≤ M * (M * |∑ j, δ j * d j|) := by
          apply mul_le_mul_of_nonneg_left hTU hM
    _ ≤ M * (M * β) := by
          apply mul_le_mul_of_nonneg_left _ hM
          apply mul_le_mul_of_nonneg_left hUbound hM
    _ = M^2 * β := by ring

-- N3 (part3)
private theorem card_cube (d : ℕ) : (Fintype.card (Fin d → Bool) : ℝ) = (2:ℝ)^d := by
  simp [Nat.cast_pow]

-- N3: orthonormality of Rademacher functions
private theorem radSign_second_moment {d : ℕ} (s : Finset (Fin d)) (a b : Fin d → ℝ) :
    ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
      = (2:ℝ)^d * ∑ k ∈ s, a k * b k := by
  have pair : ∀ k ∈ s, ∀ l ∈ s,
      (∑ ω : Fin d → Bool, (radSign k ω * a k) * (radSign l ω * b l))
        = (if l = k then (2:ℝ)^d else 0) * (a k * b l) := by
    intro k _ l _
    have e1 : ∀ ω : Fin d → Bool, (radSign k ω * a k) * (radSign l ω * b l)
        = (a k * b l) * (radSign k ω * radSign l ω) := fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => e1 ω), ← Finset.mul_sum]
    split_ifs with hkl
    · subst hkl
      have e2 : (∑ ω : Fin d → Bool, radSign l ω * radSign l ω)
          = ∑ _ω : Fin d → Bool, (1:ℝ) :=
        Finset.sum_congr rfl (fun ω _ => radSign_sq l ω)
      rw [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
      ring
    · have hne : k ≠ l := fun h => hkl h.symm
      have e2 : (∑ ω : Fin d → Bool, radSign k ω * radSign l ω) = 0 := by
        have h := radSign_flip_sum_eq_zero (d := d) l (fun ω => radSign k ω)
          (fun ω => radSign_flip_ne hne ω)
        exact h
      rw [e2, mul_zero, zero_mul]
  have step : ∀ ω : Fin d → Bool,
      (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
        = ∑ k ∈ s, ∑ l ∈ s, (radSign k ω * a k) * (radSign l ω * b l) := by
    intro ω
    exact Finset.sum_mul_sum s s _ _
  calc ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k) * (∑ l ∈ s, radSign l ω * b l)
        = ∑ k ∈ s, ∑ l ∈ s, ∑ ω : Fin d → Bool,
            (radSign k ω * a k) * (radSign l ω * b l) := by
          rw [Finset.sum_congr rfl (fun ω _ => step ω), Finset.sum_comm]
          exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = ∑ k ∈ s, ∑ l ∈ s, (if l = k then (2:ℝ)^d else 0) * (a k * b l) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          exact pair k hk l hl
      _ = ∑ k ∈ s, (2:ℝ)^d * (a k * b k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have e : ∀ l ∈ s, (if l = k then (2:ℝ)^d else 0) * (a k * b l)
              = (if l = k then (2:ℝ)^d * (a k * b l) else 0) := by
            intro l _
            split_ifs with h <;> ring
          rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
          simp [hk]
      _ = (2:ℝ)^d * ∑ k ∈ s, a k * b k := by
          rw [Finset.mul_sum]

-- N4 (part4)
-- pointwise fourth-power expansion under r*r = 1
private theorem fourth_expand {u rr c : ℝ} (hrr : rr * rr = 1) :
    (u + rr * c)^4
      = u^4 + 4 * c * (u^3 * rr) + 6 * c^2 * u^2 + 4 * c^3 * (u * rr) + c^4 := by
  have hrr2 : rr^2 = 1 := by
    have : rr^2 = rr * rr := by ring
    rw [this, hrr]
  have hrr3 : rr^3 = rr := by
    calc rr^3 = rr^2 * rr := by ring
      _ = 1 * rr := by rw [hrr2]
      _ = rr := one_mul rr
  have hrr4 : rr^4 = 1 := by
    calc rr^4 = rr^2 * rr^2 := by ring
      _ = 1 * 1 := by rw [hrr2]
      _ = 1 := one_mul 1
  have binom : (u + rr * c)^4
      = u^4 + 4*u^3*(rr*c) + 6*u^2*(rr*c)^2 + 4*u*(rr*c)^3 + (rr*c)^4 := by ring
  have sq : (rr*c)^2 = c^2 := by
    calc (rr*c)^2 = rr^2*c^2 := by ring
      _ = 1 * c^2 := by rw [hrr2]
      _ = c^2 := one_mul _
  have cb : (rr*c)^3 = c^3*rr := by
    calc (rr*c)^3 = rr^3*c^3 := by ring
      _ = rr * c^3 := by rw [hrr3]
      _ = c^3*rr := mul_comm _ _
  have q4 : (rr*c)^4 = c^4 := by
    calc (rr*c)^4 = rr^4*c^4 := by ring
      _ = 1 * c^4 := by rw [hrr4]
      _ = c^4 := one_mul _
  rw [binom, sq, cb, q4]
  ring

-- N4: fourth-moment Khintchine bound with constant 3
private theorem radSign_fourth_moment_le {d : ℕ} (s : Finset (Fin d)) (a : Fin d → ℝ) :
    ∑ ω : Fin d → Bool, (∑ k ∈ s, radSign k ω * a k)^4
      ≤ 3 * (2:ℝ)^d * (∑ k ∈ s, a k ^ 2)^2 := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j t hjt ih
    -- abbreviate the old sum and old squares
    set U : (Fin d → Bool) → ℝ := fun ω => ∑ k ∈ t, radSign k ω * a k with hU
    set S : ℝ := ∑ k ∈ t, a k ^ 2 with hS
    have hUinv : ∀ ω, U (flipAt j ω) = U ω := by
      intro ω
      simp only [hU]
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≠ j := fun h => hjt (h ▸ hk)
      rw [radSign_flip_ne hkj]
    have odd3 : (∑ ω : Fin d → Bool, U ω ^ 3 * radSign j ω) = 0 := by
      have h := radSign_flip_sum_eq_zero (d := d) j (fun ω => U ω ^ 3)
        (fun ω => by rw [hUinv ω])
      simpa [pow_three, mul_assoc] using h
    have odd1 : (∑ ω : Fin d → Bool, U ω * radSign j ω) = 0 :=
      radSign_flip_sum_eq_zero (d := d) j U hUinv
    have sqU : (∑ ω : Fin d → Bool, U ω ^ 2) = (2:ℝ)^d * S := by
      have h := radSign_second_moment (d := d) t a a
      have e1 : (∑ ω : Fin d → Bool, U ω ^ 2)
          = ∑ ω : Fin d → Bool, (∑ k ∈ t, radSign k ω * a k)
              * (∑ k ∈ t, radSign k ω * a k) := by
        simp only [hU]
        apply Finset.sum_congr rfl
        intro ω _
        rw [sq]
      have e2 : (∑ k ∈ t, a k * a k) = S := by
        simp only [hS]
        apply Finset.sum_congr rfl
        intro k _
        rw [sq]
      rw [e1, ← e2]
      exact h
    have const4 : (∑ _ω : Fin d → Bool, (a j)^4) = (2:ℝ)^d * (a j)^4 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
    -- expand the new sum
    have expand : ∀ ω : Fin d → Bool,
        (∑ k ∈ insert j t, radSign k ω * a k)^4
        = U ω^4 + 4 * a j * (U ω^3 * radSign j ω)
          + 6 * (a j)^2 * U ω^2 + 4 * (a j)^3 * (U ω * radSign j ω) + (a j)^4 := by
      intro ω
      have eU : (∑ k ∈ insert j t, radSign k ω * a k)
          = U ω + radSign j ω * a j := by
        simp only [hU]
        rw [Finset.sum_insert hjt]
        ring
      rw [eU]
      exact fourth_expand (radSign_sq j ω)
    have h2d : (0:ℝ) ≤ (2:ℝ)^d := by positivity
    have hS2 : (0:ℝ) ≤ S^2 := sq_nonneg S
    have haj4 : (0:ℝ) ≤ ((2:ℝ)^d) * (a j)^4 := by positivity
    calc ∑ ω : Fin d → Bool, (∑ k ∈ insert j t, radSign k ω * a k)^4
          = ∑ ω : Fin d → Bool, (U ω^4 + 4 * a j * (U ω^3 * radSign j ω)
              + 6 * (a j)^2 * U ω^2 + 4 * (a j)^3 * (U ω * radSign j ω) + (a j)^4) := by
            apply Finset.sum_congr rfl
            intro ω _
            exact expand ω
        _ = (∑ ω : Fin d → Bool, U ω^4)
              + 4 * a j * (∑ ω : Fin d → Bool, U ω^3 * radSign j ω)
              + 6 * (a j)^2 * (∑ ω : Fin d → Bool, U ω^2)
              + 4 * (a j)^3 * (∑ ω : Fin d → Bool, U ω * radSign j ω)
              + (∑ _ω : Fin d → Bool, (a j)^4) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ ω : Fin d → Bool, U ω^4)
              + 6 * (a j)^2 * ((2:ℝ)^d * S) + ((2:ℝ)^d * (a j)^4) := by
            rw [odd3, odd1, sqU, const4]
            ring
        _ ≤ 3 * (2:ℝ)^d * S^2 + 6 * (a j)^2 * ((2:ℝ)^d * S)
              + 3 * ((2:ℝ)^d * (a j)^4) := by
            have h := ih
            simp only [hS] at h
            have hle : (∑ ω : Fin d → Bool, U ω ^ 4) ≤ 3 * (2:ℝ)^d * S^2 := by
              simpa [hU] using h
            have h34 : (2:ℝ)^d * (a j)^4 ≤ 3 * ((2:ℝ)^d * (a j)^4) := by
              linarith [haj4]
            linarith
        _ = 3 * (2:ℝ)^d * (S + (a j)^2)^2 := by ring
        _ = 3 * (2:ℝ)^d * (∑ k ∈ insert j t, a k ^ 2)^2 := by
            rw [Finset.sum_insert hjt, hS]
            ring

-- N6-N8 (part5)
-- N6: finite families embed isometrically into some EuclideanSpace
private theorem exists_euclidean_isometric_copy {m n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin m → E) (y : Fin n → E) :
    ∃ d : ℕ, ∃ X : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ Y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖X i‖ = ‖x i‖) ∧ (∀ j, ‖Y j‖ = ‖y j‖) ∧
      (∀ i j, ⟪X i, Y j⟫_ℝ = ⟪x i, y j⟫_ℝ) := by
  have hfin : (Set.range x ∪ Set.range y).Finite :=
    (Set.finite_range x).union (Set.finite_range y)
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y)) :=
    FiniteDimensional.span_of_finite ℝ hfin
  let b := stdOrthonormalBasis ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y))
  refine ⟨Module.finrank ℝ (Submodule.span ℝ (Set.range x ∪ Set.range y)),
    fun i => b.repr ⟨x i, Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i))⟩,
    fun j => b.repr ⟨y j, Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self j))⟩,
    ?_, ?_, ?_⟩
  · intro i
    rw [b.repr.norm_map]
    exact (Submodule.norm_coe _).symm
  · intro j
    rw [b.repr.norm_map]
    exact (Submodule.norm_coe _).symm
  · intro i j
    rw [b.repr.inner_map_map]
    exact Submodule.coe_inner _ _ _

/-- Supremum of `|∑ A ⟪x, y⟫|` over Euclidean unit-ball families. -/
private noncomputable def gtBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
    ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
    (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| }

-- N7
private theorem gtBound_mem_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (0:ℝ) ∈ { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => by simp, fun _ => by simp, ?_⟩
  simp

private theorem gtBound_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  intro r hr
  obtain ⟨d, x, y, hx, hy, rfl⟩ := hr
  calc |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ|
        ≤ ∑ i, |∑ j, A i j * ⟪x i, y j⟫_ℝ| :=
          Finset.abs_sum_le_sum_abs (fun i => ∑ j, A i j * ⟪x i, y j⟫_ℝ) Finset.univ
      _ ≤ ∑ i, ∑ j, |A i j * ⟪x i, y j⟫_ℝ| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.abs_sum_le_sum_abs (fun j => A i j * ⟪x i, y j⟫_ℝ) Finset.univ
      _ ≤ ∑ i, ∑ j, |A i j| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hinner : |⟪x i, y j⟫_ℝ| ≤ 1 := by
            calc |⟪x i, y j⟫_ℝ| ≤ ‖x i‖ * ‖y j‖ := abs_real_inner_le_norm _ _
              _ ≤ 1 * 1 := by
                  apply mul_le_mul (hx i) (hy j) (norm_nonneg _) (by norm_num)
              _ = 1 := one_mul 1
          calc |A i j| * |⟪x i, y j⟫_ℝ| ≤ |A i j| * 1 := by
                apply mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
            _ = |A i j| := mul_one _

private theorem gtBound_le_of_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {r : ℝ} (hr : r ∈ { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| }) :
    r ≤ gtBound A :=
  le_csSup (gtBound_bdd A) hr

private theorem gtBound_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ gtBound A :=
  le_csSup (gtBound_bdd A) (gtBound_mem_zero A)

-- N8: transfer bound for arbitrary real inner product spaces
private theorem abs_sum_inner_le_gtBound_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a : Fin m → E) (b : Fin n → E) (ha : ∀ i, ‖a i‖ ≤ s) (hb : ∀ j, ‖b j‖ ≤ t) :
    |∑ i, ∑ j, A i j * ⟪a i, b j⟫_ℝ| ≤ gtBound A * s * t := by
  by_cases hs0 : s = 0
  · subst hs0
    have ha0 : ∀ i, a i = 0 := fun i => norm_le_zero_iff.mp (by simpa using ha i)
    simp [ha0]
  · by_cases ht0 : t = 0
    · subst ht0
      have hb0 : ∀ j, b j = 0 := fun j => norm_le_zero_iff.mp (by simpa using hb j)
      simp [hb0]
    · have hapos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hbpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      let a' : Fin m → E := fun i => s⁻¹ • a i
      let b' : Fin n → E := fun j => t⁻¹ • b j
      have ha' : ∀ i, ‖a' i‖ ≤ 1 := by
        intro i
        have e : ‖a' i‖ = s⁻¹ * ‖a i‖ := by
          simp only [a', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
        rw [e]
        calc s⁻¹ * ‖a i‖ ≤ s⁻¹ * s := by
              apply mul_le_mul_of_nonneg_left (ha i) (le_of_lt (inv_pos.mpr hapos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hapos)
      have hb' : ∀ j, ‖b' j‖ ≤ 1 := by
        intro j
        have e : ‖b' j‖ = t⁻¹ * ‖b j‖ := by
          simp only [b', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
        rw [e]
        calc t⁻¹ * ‖b j‖ ≤ t⁻¹ * t := by
              apply mul_le_mul_of_nonneg_left (hb j) (le_of_lt (inv_pos.mpr hbpos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hbpos)
      obtain ⟨d, X, Y, hXn, hYn, hXY⟩ :=
        exists_euclidean_isometric_copy (m := m) (n := n) (E := E) a' b'
      have hX1 : ∀ i, ‖X i‖ ≤ 1 := fun i => by rw [hXn i]; exact ha' i
      have hY1 : ∀ j, ‖Y j‖ ≤ 1 := fun j => by rw [hYn j]; exact hb' j
      have hmem : |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ∈
          { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
            ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
            (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧
            r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } :=
        ⟨d, X, Y, hX1, hY1, rfl⟩
      have hle : |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ≤ gtBound A :=
        gtBound_le_of_mem A hmem
      have eab : ∀ i j, A i j * ⟪a i, b j⟫_ℝ = (s * t) * (A i j * ⟪a' i, b' j⟫_ℝ) := by
        intro i j
        have e1 : a i = s • a' i := by
          simp only [a', ← mul_smul, mul_inv_cancel₀ (ne_of_gt hapos), one_smul]
        have e2 : b j = t • b' j := by
          simp only [b', ← mul_smul, mul_inv_cancel₀ (ne_of_gt hbpos), one_smul]
        rw [e1, e2, real_inner_smul_left, real_inner_smul_right]
        ring
      have eXY : (∑ i, ∑ j, A i j * ⟪a' i, b' j⟫_ℝ)
          = ∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hXY i j]
      have esum : (∑ i, ∑ j, A i j * ⟪a i, b j⟫_ℝ)
          = (s * t) * (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ) := by
        rw [← eXY]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact eab i j
      rw [esum, abs_mul]
      have hst : |s * t| = s * t := abs_of_nonneg (mul_nonneg hs ht)
      rw [hst]
      calc s * t * |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ|
            ≤ s * t * gtBound A := by
              apply mul_le_mul_of_nonneg_left hle (mul_nonneg hs ht)
        _ = gtBound A * s * t := by ring

-- N9-N10 (part6)
-- N9a
private theorem radEmbed_moment_a {d : ℕ} (X Y : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed Y ω = (2:ℝ)^d * ⟪X, Y⟫_ℝ := by
  have h := radSign_second_moment (d := d) Finset.univ (fun k => X k) (fun k => Y k)
  have eXY : (∑ k ∈ Finset.univ, X k * Y k) = ⟪X, Y⟫_ℝ := by
    simp [PiLp.inner_apply, mul_comm]
  calc ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed Y ω
        = ∑ ω : Fin d → Bool, (∑ k ∈ Finset.univ, radSign k ω * X k)
          * (∑ l ∈ Finset.univ, radSign l ω * Y l) := rfl
      _ = (2:ℝ)^d * ∑ k ∈ Finset.univ, X k * Y k := h
      _ = (2:ℝ)^d * ⟪X, Y⟫_ℝ := by rw [eXY]

-- N9b
private theorem radEmbed_moment_b {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, (radEmbed X ω)^2 = (2:ℝ)^d * ‖X‖^2 := by
  calc ∑ ω : Fin d → Bool, (radEmbed X ω)^2
        = ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed X ω :=
          Finset.sum_congr rfl (fun ω _ => sq (radEmbed X ω))
      _ = (2:ℝ)^d * ⟪X, X⟫_ℝ := radEmbed_moment_a X X
      _ = (2:ℝ)^d * ‖X‖^2 := by rw [real_inner_self_eq_norm_sq]

-- N9c
private theorem radEmbed_moment_c {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, (radEmbed X ω)^4 ≤ 3 * (2:ℝ)^d * ‖X‖^4 := by
  have h := radSign_fourth_moment_le (d := d) Finset.univ (fun k => X k)
  have erhs : (∑ k ∈ Finset.univ, X k ^ 2) = ‖X‖^2 :=
    (EuclideanSpace.real_norm_sq_eq X).symm
  calc ∑ ω : Fin d → Bool, (radEmbed X ω)^4
        = ∑ ω : Fin d → Bool, (∑ k ∈ Finset.univ, radSign k ω * X k)^4 := rfl
      _ ≤ 3 * (2:ℝ)^d * (∑ k ∈ Finset.univ, X k ^ 2)^2 := h
      _ = 3 * (2:ℝ)^d * ‖X‖^4 := by
          rw [erhs]
          ring

/-- Scale for the uniform measure on the cube. -/
private noncomputable def cubeScale (d : ℕ) : ℝ := Real.sqrt (((2:ℝ)^d)⁻¹)

private theorem cubeScale_sq (d : ℕ) : cubeScale d * cubeScale d = ((2:ℝ)^d)⁻¹ :=
  Real.mul_self_sqrt (by positivity)

/-- Embed a function on the cube as a Euclidean vector with uniform-measure scaling. -/
private noncomputable def scaledVec {d : ℕ} (f : (Fin d → Bool) → ℝ) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  WithLp.toLp 2 (fun ω => cubeScale d * f ω)

-- N10i
private theorem scaledVec_inner {d : ℕ} (f g : (Fin d → Bool) → ℝ) :
    ⟪scaledVec f, scaledVec g⟫_ℝ = ((2:ℝ)^d)⁻¹ * ∑ ω, f ω * g ω := by
  have e : ⟪scaledVec f, scaledVec g⟫_ℝ
      = ∑ ω, (cubeScale d * f ω) * (cubeScale d * g ω) := by
    simp [scaledVec, PiLp.inner_apply, mul_comm]
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc (cubeScale d * f ω) * (cubeScale d * g ω)
        = (cubeScale d * cubeScale d) * (f ω * g ω) := by ring
      _ = ((2:ℝ)^d)⁻¹ * (f ω * g ω) := by rw [cubeScale_sq]

-- N10ii
private theorem scaledVec_norm_sq {d : ℕ} (f : (Fin d → Bool) → ℝ) :
    ‖scaledVec f‖^2 = ((2:ℝ)^d)⁻¹ * ∑ ω, f ω ^ 2 := by
  have e : ‖scaledVec f‖^2 = ∑ ω, (cubeScale d * f ω)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro ω _
    rfl
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc (cubeScale d * f ω)^2
        = (cubeScale d * cubeScale d) * (f ω ^ 2) := by ring
      _ = ((2:ℝ)^d)⁻¹ * (f ω ^ 2) := by rw [cubeScale_sq]

-- N10iii
private theorem scaledVec_add {d : ℕ} (f g : (Fin d → Bool) → ℝ) :
    scaledVec (fun ω => f ω + g ω) = scaledVec f + scaledVec g := by
  unfold scaledVec
  ext ω
  simp [mul_add]

-- N10iv
private theorem scaledVec_norm_le {d : ℕ} (f : (Fin d → Bool) → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ((2 : ℝ) ^ d)⁻¹ * ∑ ω, f ω ^ 2 ≤ ρ ^ 2) :
    ‖scaledVec f‖ ≤ ρ := by
  have h2 : ‖scaledVec f‖^2 ≤ ρ^2 := by
    rw [scaledVec_norm_sq]
    exact h
  have habs := abs_le_of_sq_le_sq h2 hρ
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

-- N11 (part6)
private noncomputable def fullV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) := scaledVec (radEmbed X)

private noncomputable def lowV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  scaledVec (fun ω => truncAt 8 (radEmbed X ω))

private noncomputable def highV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  scaledVec (fun ω => radEmbed X ω - truncAt 8 (radEmbed X ω))

-- N11a
private theorem fullV_eq {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    fullV X = lowV X + highV X := by
  change scaledVec (radEmbed X) = scaledVec _ + scaledVec _
  rw [← scaledVec_add]
  congr 1
  funext ω
  change radEmbed X ω
    = truncAt 8 (radEmbed X ω) + (radEmbed X ω - truncAt 8 (radEmbed X ω))
  exact Eq.symm (add_sub_cancel (truncAt 8 (radEmbed X ω)) (radEmbed X ω))

-- N11b
private theorem fullV_inner {d : ℕ} (X Y : EuclideanSpace ℝ (Fin d)) :
    ⟪fullV X, fullV Y⟫_ℝ = ⟪X, Y⟫_ℝ := by
  change ⟪scaledVec (radEmbed X), scaledVec (radEmbed Y)⟫_ℝ = _
  rw [scaledVec_inner, radEmbed_moment_a]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]

-- N11c
private theorem fullV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖fullV X‖ ≤ 1 := by
  change ‖scaledVec (radEmbed X)‖ ≤ 1
  apply scaledVec_norm_le _ (by norm_num)
  have h2 := radEmbed_moment_b (d := d) X
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω)^2
        = ((2:ℝ)^d)⁻¹ * ((2:ℝ)^d * ‖X‖^2) := by rw [h2]
      _ = ‖X‖^2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
      _ ≤ 1 := h12
      _ = 1^2 := (one_pow 2).symm

-- N11d
private theorem lowV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖lowV X‖ ≤ 1 := by
  change ‖scaledVec (fun ω => truncAt 8 (radEmbed X ω))‖ ≤ 1
  apply scaledVec_norm_le _ (by norm_num)
  have h2 := radEmbed_moment_b (d := d) X
  have hle : (∑ ω, (truncAt 8 (radEmbed X ω))^2) ≤ ∑ ω, (radEmbed X ω)^2 := by
    apply Finset.sum_le_sum
    intro ω _
    exact (truncAt_facts (show (0:ℝ) < 8 by norm_num)).2.1
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (truncAt 8 (radEmbed X ω))^2
        ≤ ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω)^2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((2:ℝ)^d)⁻¹ * ((2:ℝ)^d * ‖X‖^2) := by rw [h2]
      _ = ‖X‖^2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
      _ ≤ 1 := h12
      _ = 1^2 := (one_pow 2).symm

-- N11e
private theorem highV_norm_le {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) (hX : ‖X‖ ≤ 1) :
    ‖highV X‖ ≤ 1/4 := by
  change ‖scaledVec (fun ω => radEmbed X ω - truncAt 8 (radEmbed X ω))‖ ≤ 1/4
  apply scaledVec_norm_le _ (by norm_num)
  have h4 := radEmbed_moment_c (d := d) X
  have htail : ∀ ω : Fin d → Bool,
      (radEmbed X ω - truncAt 8 (radEmbed X ω))^2 ≤ (radEmbed X ω)^4 / 64 := by
    intro ω
    have h := (truncAt_facts (show (0:ℝ) < 8 by norm_num)
      (t := radEmbed X ω)).2.2
    have h64 : (8:ℝ)^2 = 64 := by norm_num
    rw [h64] at h
    exact (le_div_iff₀ (show (0:ℝ) < 64 by norm_num)).mpr h
  have hsum : (∑ ω : Fin d → Bool, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2)
      ≤ (∑ ω : Fin d → Bool, (radEmbed X ω)^4) / 64 := by
    calc (∑ ω : Fin d → Bool, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2)
          ≤ ∑ ω : Fin d → Bool, ((radEmbed X ω)^4 / 64) :=
            Finset.sum_le_sum (fun ω _ => htail ω)
        _ = (∑ ω : Fin d → Bool, (radEmbed X ω)^4) / 64 :=
            (Finset.sum_div _ _ _).symm
  have h12 : ‖X‖^2 ≤ 1 := by nlinarith [norm_nonneg X, hX]
  have h14 : ‖X‖^4 ≤ 1 := by
    have e : ‖X‖^4 = (‖X‖^2)^2 := by ring
    rw [e]
    calc (‖X‖^2)^2 ≤ 1^2 := pow_le_pow_left₀ (sq_nonneg _) h12 2
      _ = 1 := one_pow 2
  have h4cancel : ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64) = 3 * ‖X‖^4 / 64 := by
    calc ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64)
          = (((2:ℝ)^d)⁻¹ * (2:ℝ)^d) * (3 * ‖X‖^4 / 64) := by ring
        _ = 3 * ‖X‖^4 / 64 := by
            rw [inv_mul_cancel₀ (by positivity : (2:ℝ)^d ≠ 0), one_mul]
  calc ((2:ℝ)^d)⁻¹ * ∑ ω, (radEmbed X ω - truncAt 8 (radEmbed X ω))^2
        ≤ ((2:ℝ)^d)⁻¹ * ((∑ ω, (radEmbed X ω)^4) / 64) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ((2:ℝ)^d)⁻¹ * ((3 * (2:ℝ)^d * ‖X‖^4) / 64) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hdiv : (∑ ω, (radEmbed X ω)^4) * (64:ℝ)⁻¹
              ≤ (3 * (2:ℝ)^d * ‖X‖^4) * 64⁻¹ :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
          simpa [div_eq_mul_inv] using hdiv
      _ = 3 * ‖X‖^4 / 64 := h4cancel
      _ ≤ 3 * 1 / 64 := by
          have hdiv : (3 * ‖X‖^4) * (64:ℝ)⁻¹ ≤ (3 * 1) * 64⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h14 (by norm_num)) (by positivity)
          simpa [div_eq_mul_inv] using hdiv
      _ ≤ (1/4)^2 := by norm_num

-- N12-N15 (part7)
-- N12: low part bounded by sign maximum
private theorem low_part_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    {d : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (Y : Fin n → EuclideanSpace ℝ (Fin d)) :
    |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ| ≤ 64 * β := by
  have efunds : ∀ i j, ⟪lowV (X i), lowV (Y j)⟫_ℝ
      = ((2:ℝ)^d)⁻¹ * ∑ ω, truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω) := by
    intro i j
    change ⟪scaledVec _, scaledVec _⟫_ℝ = _
    rw [scaledVec_inner]
  have step1 : ∀ i j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ
      = ((2:ℝ)^d)⁻¹ * (∑ ω,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
    intro i j
    have e1 : A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ
        = ((2:ℝ)^d)⁻¹ * (A i j * (∑ ω,
            truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))) := by
      rw [efunds i j]; ring
    have e2 : A i j * (∑ ω, truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))
        = ∑ ω, A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      exact (mul_assoc _ _ _).symm
    rw [e1, e2]
  have esum : (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
      = ((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
        A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
    calc (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
          = ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ * (∑ ω,
              A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step1 i j))
        _ = ∑ i, ∑ j, ∑ ω : Fin d → Bool, ((2:ℝ)^d)⁻¹ *
            (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            simp only [Finset.mul_sum]
        _ = ∑ ω : Fin d → Bool, ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ *
            (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            calc (∑ i, ∑ j, ∑ ω : Fin d → Bool, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)))
                  = ∑ i, ∑ ω : Fin d → Bool, ∑ j, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
                    apply Finset.sum_congr rfl; intro i _
                    exact Finset.sum_comm
                _ = ∑ ω : Fin d → Bool, ∑ i, ∑ j, ((2:ℝ)^d)⁻¹ *
                    (A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) :=
                    Finset.sum_comm
        _ = ((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
            A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)) := by
            simp only [← Finset.mul_sum]
  have hF : ∀ ω : Fin d → Bool,
      |∑ i, ∑ j, A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)|
        ≤ 64 * β := by
    intro ω
    have h1 := abs_bilinear_le_sq_mul_of_sign_bound (m := m) (n := n) A (M := 8) (β := β)
      (by norm_num) hsign
      (fun i => truncAt 8 (radEmbed (X i) ω)) (fun j => truncAt 8 (radEmbed (Y j) ω))
      (fun i => (truncAt_facts (show (0:ℝ) < 8 by norm_num)).1)
      (fun j => (truncAt_facts (show (0:ℝ) < 8 by norm_num)).1)
    have e : (8:ℝ)^2 * β = 64 * β := by ring
    rwa [e] at h1
  have hpos : (0:ℝ) ≤ ((2:ℝ)^d)⁻¹ := by positivity
  have hcard : (0:ℝ) < ((2:ℝ)^d) := by positivity
  calc |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ|
        = |((2:ℝ)^d)⁻¹ * ∑ ω : Fin d → Bool, (∑ i, ∑ j,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))| := by
          rw [esum]
      _ = ((2:ℝ)^d)⁻¹ * |∑ ω : Fin d → Bool, (∑ i, ∑ j,
          A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))| := by
          rw [abs_mul, abs_of_nonneg hpos]
      _ ≤ ((2:ℝ)^d)⁻¹ * (Fintype.card (Fin d → Bool) * (64 * β)) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          calc |∑ ω : Fin d → Bool, (∑ i, ∑ j,
                  A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω))|
                ≤ ∑ ω : Fin d → Bool, |∑ i, ∑ j,
                  A i j * truncAt 8 (radEmbed (X i) ω) * truncAt 8 (radEmbed (Y j) ω)| :=
                  Finset.abs_sum_le_sum_abs _ Finset.univ
              _ ≤ ∑ _ω : Fin d → Bool, (64 * β) :=
                  Finset.sum_le_sum (fun ω _ => hF ω)
              _ = Fintype.card (Fin d → Bool) * (64 * β) := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 64 * β := by
          rw [card_cube, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul]

-- N13
private theorem euclidean_self_improving_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β)
    {d : ℕ} (X : Fin m → EuclideanSpace ℝ (Fin d))
    (Y : Fin n → EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, ‖X i‖ ≤ 1) (hY : ∀ j, ‖Y j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ≤ 64 * β + gtBound A / 2 := by
  have e1 : ∀ i j, ⟪X i, Y j⟫_ℝ
      = ⟪lowV (X i), lowV (Y j)⟫_ℝ + ⟪highV (X i), fullV (Y j)⟫_ℝ
        + ⟪lowV (X i), highV (Y j)⟫_ℝ := by
    intro i j
    have hfull : ⟪X i, Y j⟫_ℝ = ⟪fullV (X i), fullV (Y j)⟫_ℝ := (fullV_inner _ _).symm
    rw [hfull, fullV_eq (X i), fullV_eq (Y j), inner_add_left, inner_add_right,
      ← fullV_eq (Y j)]
    ring
  have per : ∀ i j, A i j * ⟪X i, Y j⟫_ℝ
      = (A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ) := by
    intro i j
    rw [e1 i j]; ring
  have hsplit : (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ)
      = (∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ) := by
    calc (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ)
          = ∑ i, ∑ j, ((A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
            + (A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
            + (A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)) :=
              Finset.sum_congr rfl
                (fun i _ => Finset.sum_congr rfl (fun j _ => per i j))
        _ = _ := by simp only [Finset.sum_add_distrib]
  have hS1 : |∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ| ≤ 64 * β :=
    low_part_bound A hsign X Y
  have hS2 : |∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ|
      ≤ gtBound A * (1/4) * 1 := by
    apply abs_sum_inner_le_gtBound_mul A (by norm_num) (by norm_num)
    · intro i
      exact highV_norm_le _ (hX i)
    · intro j
      exact fullV_norm_le _ (hY j)
  have hS3 : |∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ|
      ≤ gtBound A * 1 * (1/4) := by
    apply abs_sum_inner_le_gtBound_mul A (by norm_num) (by norm_num)
    · intro i
      exact lowV_norm_le _ (hX i)
    · intro j
      exact highV_norm_le _ (hY j)
  rw [hsplit]
  calc |(∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)
        + (∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)|
        ≤ |(∑ i, ∑ j, A i j * ⟪lowV (X i), lowV (Y j)⟫_ℝ)|
          + |(∑ i, ∑ j, A i j * ⟪highV (X i), fullV (Y j)⟫_ℝ)|
          + |(∑ i, ∑ j, A i j * ⟪lowV (X i), highV (Y j)⟫_ℝ)| :=
          abs_add_three _ _ _
      _ ≤ (64 * β) + (gtBound A * (1/4) * 1) + (gtBound A * 1 * (1/4)) :=
          add_le_add (add_le_add hS1 hS2) hS3
      _ = 64 * β + gtBound A / 2 := by ring

-- N14
private theorem gtBound_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {β : ℝ}
    (hsign : ∀ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) → (∀ j, δ j = 1 ∨ δ j = -1) →
      |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| ≤ β) :
    gtBound A ≤ 128 * β := by
  have hstep : gtBound A ≤ 64 * β + gtBound A / 2 := by
    unfold gtBound
    apply csSup_le ⟨0, gtBound_mem_zero A⟩
    intro r hr
    obtain ⟨d, x, y, hx, hy, rfl⟩ := hr
    exact euclidean_self_improving_bound A hsign x y hx hy
  linarith

-- N15: the Wanted statement, K = 128
/--
**Grothendieck's inequality (real case).** There is a constant $K > 0$ such that for all
$m, n \in \mathbb{N}$, every real $m \times n$ matrix $A = (a_{ij})$, every real Hilbert space $H$
and all vectors $x_1, \dots, x_m, y_1, \dots, y_n \in H$ of norm at most $1$, there are signs
$\varepsilon_1, \dots, \varepsilon_m, \delta_1, \dots, \delta_n \in \{1, -1\}$ such that
$\bigl|\sum_{i=1}^{m} \sum_{j=1}^{n} a_{ij} \langle x_i, y_j \rangle\bigr| \le
K \bigl|\sum_{i=1}^{m} \sum_{j=1}^{n} a_{ij} \varepsilon_i \delta_j\bigr|$.

Proves `Wanted` entry `grothendieck_inequality_real`.

Source: A. Grothendieck, Resume de la theorie
metrique des produits tensoriels topologiques, Bol. Soc. Mat. Sao Paulo 8 (1953) 1-79, inequality;
Pisier, Grothendieck's theorem past and present, 2012; Lean states real finite-matrix scalarized
form with `Fin`-indexed unit vectors and `±1` signs, existential universal constant `K`.
-/
theorem grothendieck_inequality_real :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (x : Fin m → H) (y : Fin n → H),
        (∀ i, ‖x i‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) →
        ∃ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          (∀ j, δ j = 1 ∨ δ j = -1) ∧
          |∑ i : Fin m, ∑ j : Fin n, A i j * ⟪x i, y j⟫_ℝ| ≤
            K * |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| := by
  refine ⟨128, by norm_num, fun m n A H _ _ _ x y hx hy => ?_⟩
  let σ : Bool → ℝ := fun b => if b then 1 else -1
  have hne : Nonempty ((Fin m → Bool) × (Fin n → Bool)) :=
    ⟨(fun _ => true, fun _ => true)⟩
  obtain ⟨⟨ps, qs⟩, hmax⟩ := @Finite.exists_max
    ((Fin m → Bool) × (Fin n → Bool)) ℝ inferInstance hne inferInstance
    (fun pq : (Fin m → Bool) × (Fin n → Bool) =>
      |∑ i, ∑ j, A i j * σ (pq.1 i) * σ (pq.2 j)|)
  refine ⟨fun i => σ (ps i), fun j => σ (qs j), ?_, ?_, ?_⟩
  · intro i
    cases h : ps i <;> simp [σ, h]
  · intro j
    cases h : qs j <;> simp [σ, h]
  · have hσε : ∀ (ε' : Fin m → ℝ), (∀ i, ε' i = 1 ∨ ε' i = -1) →
        ∀ i, σ (decide (ε' i = 1)) = ε' i := by
      intro ε' hε' i
      simp only [σ]
      split_ifs with hd
      · exact (of_decide_eq_true hd).symm
      · have hne : ¬ ε' i = 1 := of_decide_eq_false (Bool.eq_false_of_ne_true hd)
        have h2 : ε' i = -1 := by
          rcases hε' i with h1 | h1
          · exact absurd h1 hne
          · exact h1
        rw [h2]
    have hσδ : ∀ (δ' : Fin n → ℝ), (∀ j, δ' j = 1 ∨ δ' j = -1) →
        ∀ j, σ (decide (δ' j = 1)) = δ' j := by
      intro δ' hδ' j
      simp only [σ]
      split_ifs with hd
      · exact (of_decide_eq_true hd).symm
      · have hne : ¬ δ' j = 1 := of_decide_eq_false (Bool.eq_false_of_ne_true hd)
        have h2 : δ' j = -1 := by
          rcases hδ' j with h1 | h1
          · exact absurd h1 hne
          · exact h1
        rw [h2]
    have hsign : ∀ (ε' : Fin m → ℝ) (δ' : Fin n → ℝ),
        (∀ i, ε' i = 1 ∨ ε' i = -1) → (∀ j, δ' j = 1 ∨ δ' j = -1) →
        |∑ i : Fin m, ∑ j : Fin n, A i j * ε' i * δ' j|
          ≤ |∑ i, ∑ j, A i j * σ (ps i) * σ (qs j)| := by
      intro ε' δ' hε' hδ'
      have erew : (∑ i, ∑ j, A i j * ε' i * δ' j)
          = ∑ i, ∑ j, A i j * σ (decide (ε' i = 1)) * σ (decide (δ' j = 1)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hσε ε' hε' i, hσδ δ' hδ' j]
      rw [erew]
      exact hmax ⟨fun i => decide (ε' i = 1), fun j => decide (δ' j = 1)⟩
    have hN8 := abs_sum_inner_le_gtBound_mul (E := H) A (s := 1) (t := 1)
      (by norm_num) (by norm_num) x y hx hy
    have hN14 := gtBound_le A hsign
    calc |∑ i : Fin m, ∑ j : Fin n, A i j * ⟪x i, y j⟫_ℝ|
          ≤ gtBound A * 1 * 1 := hN8
        _ = gtBound A := by ring
        _ ≤ 128 * |∑ i, ∑ j, A i j * σ (ps i) * σ (qs j)| := hN14
        _ = 128 * |∑ i : Fin m, ∑ j : Fin n,
            A i j * (fun i => σ (ps i)) i * (fun j => σ (qs j)) j| := rfl

end MathlibExt.Analysis.FunctionalAnalysis.GrothendieckInequalityWanted
end
