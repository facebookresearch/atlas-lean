/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sublinear expectation spaces, independence and the G-normal distribution

Peng's sublinear expectation space `(Ω, H, E)`: `H` is a space of real functions on `Ω` closed
under `φ(X₁, …, Xₙ)` for every `φ` in `C_{l.Lip}(ℝⁿ)` (locally Lipschitz with a polynomially
growing constant), and `E` is a sublinear expectation on `H`. Distributions and independence are
defined through `E` alone (S. Peng, *Nonlinear Expectations and Stochastic Calculus under
Uncertainty*, arXiv:1002.4546v1, 2010, Chapter I, §§1 and 3):

* `IdentDistrib`: `X₁ =ᵈ X₂` iff `E₁[φ(X₁)] = E₂[φ(X₂)]` for all `φ ∈ C_{l.Lip}` (Definition I.3.1);
* `IndepFrom S Y X`: `Y` is independent from `X` iff `E[φ(X, Y)] = E[E[φ(x, Y)]_{x = X}]`
  (Definition I.3.10). This relation is *not* symmetric (Remark I.3.12).
* `IsGNormal`: a real random variable `X` is (centred) G-normal if `aX + bX̄ =ᵈ √(a² + b²) X`
  for `a, b ≥ 0`, where `X̄` is an independent copy of `X` (Definition II.1.4, `d = 1`).
* `IsGNormal.expectation_eq_zero`, `IsGNormal.expectation_neg_eq_zero`: a G-normal random
  variable has no mean uncertainty, `E[X] = E[-X] = 0` (Remark II.1.5).
-/

@[expose] public section

namespace MathlibExt.Probability.SublinearExpectation

/-- **Peng's test-function class `C_{l.Lip}`** (S. Peng, arXiv:1002.4546v1, Chapter I, §1): `φ`
satisfies `|φ(x) - φ(y)| ≤ C (1 + ‖x‖ᵐ + ‖y‖ᵐ) ‖x - y‖` for some `C` and some `m ∈ ℕ`. The class
does not depend on the choice of an equivalent norm. -/
def IsLocLip {F : Type*} [SeminormedAddCommGroup F] (φ : F → ℝ) : Prop :=
  ∃ C : ℝ, ∃ m : ℕ, ∀ x y, |φ x - φ y| ≤ C * (1 + ‖x‖ ^ m + ‖y‖ ^ m) * ‖x - y‖

/-- **Constants are test functions.** A constant function is in `C_{l.Lip}`. -/
theorem isLocLip_const {F : Type*} [SeminormedAddCommGroup F] (c : ℝ) :
    IsLocLip (fun _ : F ↦ c) :=
  ⟨0, 0, fun x y ↦ by simp⟩

/-- **Lipschitz functions are test functions.** A Lipschitz function is in `C_{l.Lip}` (with
`m = 0`). -/
theorem isLocLip_of_lipschitzWith {F : Type*} [SeminormedAddCommGroup F] {K : NNReal}
    {φ : F → ℝ} (hφ : LipschitzWith K φ) : IsLocLip φ := by
  refine ⟨K, 0, fun x y ↦ ?_⟩
  have h := hφ.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at h
  have hn : 0 ≤ (K : ℝ) * ‖x - y‖ := mul_nonneg K.2 (norm_nonneg _)
  simp only [pow_zero]
  nlinarith [norm_nonneg (x - y)]

/-- **Sublinear expectation space** (S. Peng, arXiv:1002.4546v1, Chapter I, Definition 1.1 with
the standing convention of §1). `H` is a set of real functions on `Ω`, closed under
`(X₁, …, Xₙ) ↦ φ(X₁, …, Xₙ)` for `φ ∈ C_{l.Lip}(ℝⁿ)` (so it is a linear space containing the
constants and `|X|` for each of its elements), and `E` is monotone, constant preserving,
subadditive and positively homogeneous on `H`. `E` is total on `Ω → ℝ`; only its values on `H`
are constrained. -/
structure SublinearExpectationSpace (Ω : Type*) where
  /-- The space of random variables. -/
  H : Set (Ω → ℝ)
  comp_mem : ∀ (n : ℕ) (X : Fin n → Ω → ℝ), (∀ i, X i ∈ H) →
    ∀ φ : (Fin n → ℝ) → ℝ, IsLocLip φ → (fun ω ↦ φ (fun i ↦ X i ω)) ∈ H
  /-- The sublinear expectation. -/
  E : (Ω → ℝ) → ℝ
  mono : ∀ X ∈ H, ∀ Y ∈ H, Y ≤ X → E Y ≤ E X
  const : ∀ c : ℝ, E (fun _ ↦ c) = c
  subadd : ∀ X ∈ H, ∀ Y ∈ H, E (X + Y) ≤ E X + E Y
  pos_hom : ∀ X ∈ H, ∀ c : ℝ, 0 ≤ c → E (c • X) = c * E X

namespace SublinearExpectationSpace

variable {Ω : Type*} (S : SublinearExpectationSpace Ω)

/-- **Constants are random variables.** Every constant function belongs to `H`. -/
theorem const_mem (c : ℝ) : (fun _ : Ω ↦ c) ∈ S.H :=
  S.comp_mem 0 Fin.elim0 (fun i ↦ i.elim0) _ (isLocLip_const c)

/-- **Sums of random variables.** `H` is closed under addition. -/
theorem add_mem {X Y : Ω → ℝ} (hX : X ∈ S.H) (hY : Y ∈ S.H) : X + Y ∈ S.H := by
  have h := S.comp_mem 2 ![X, Y] (fun i ↦ by fin_cases i <;> simpa) (fun x ↦ x 0 + x 1) ⟨1, 0,
    fun x y ↦ by
      have h0 : |x 0 - y 0| ≤ ‖x - y‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) 0
      have h1 : |x 1 - y 1| ≤ ‖x - y‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) 1
      have : |x 0 + x 1 - (y 0 + y 1)| ≤ |x 0 - y 0| + |x 1 - y 1| := by
        rw [show x 0 + x 1 - (y 0 + y 1) = (x 0 - y 0) + (x 1 - y 1) by ring]
        exact abs_add_le _ _
      simp only [pow_zero]
      nlinarith [norm_nonneg (x - y)]⟩
  convert h using 1
  ext ω
  simp

/-- **Cash translatability** (S. Peng, arXiv:1002.4546v1, Chapter I, Remark 1.4 (vi)):
`E[c + X] = c + E[X]`. -/
theorem expectation_const_add {X : Ω → ℝ} (hX : X ∈ S.H) (c : ℝ) :
    S.E (fun ω ↦ c + X ω) = c + S.E X := by
  have hcX : (fun ω ↦ c + X ω) ∈ S.H := S.add_mem (S.const_mem c) hX
  have h1 := S.subadd _ (S.const_mem c) _ hX
  have h2 := S.subadd _ hcX _ (S.const_mem (-c))
  have e1 : ((fun _ : Ω ↦ c) + X) = fun ω ↦ c + X ω := rfl
  have e2 : ((fun ω ↦ c + X ω) + fun _ : Ω ↦ -c) = X := by ext ω; simp
  rw [e1, S.const] at h1
  rw [e2, S.const] at h2
  linarith

/-- **Identically distributed random vectors** (S. Peng, arXiv:1002.4546v1, Chapter I,
Definition 3.1). `X₁` on `S₁` and `X₂` on `S₂`, with values in a normed group `F`, are
identically distributed if `E₁[φ(X₁)] = E₂[φ(X₂)]` for every `φ ∈ C_{l.Lip}(F)`. -/
def IdentDistrib {Ω₁ Ω₂ F : Type*} [SeminormedAddCommGroup F] (S₁ : SublinearExpectationSpace Ω₁)
    (S₂ : SublinearExpectationSpace Ω₂) (X₁ : Ω₁ → F) (X₂ : Ω₂ → F) : Prop :=
  ∀ φ : F → ℝ, IsLocLip φ → S₁.E (fun ω ↦ φ (X₁ ω)) = S₂.E (fun ω ↦ φ (X₂ ω))

/-- **Independence under a sublinear expectation** (S. Peng, arXiv:1002.4546v1, Chapter I,
Definition 3.10). `Y` is independent from `X` if `E[φ(X, Y)] = E[E[φ(x, Y)]_{x = X}]` for every
`φ ∈ C_{l.Lip}`. The relation is not symmetric in `X` and `Y` (Remark 3.12 there). -/
def IndepFrom {F₁ F₂ : Type*} [SeminormedAddCommGroup F₁] [SeminormedAddCommGroup F₂]
    (Y : Ω → F₂) (X : Ω → F₁) : Prop :=
  ∀ φ : F₁ × F₂ → ℝ, IsLocLip φ →
    S.E (fun ω ↦ φ (X ω, Y ω)) = S.E (fun ω ↦ S.E (fun ω' ↦ φ (X ω, Y ω')))

/-- **G-normal distribution, one-dimensional** (S. Peng, arXiv:1002.4546v1, Chapter II,
Definition 1.4 with `d = 1`). A real random variable `X ∈ H` is (centred) G-normally distributed
if it has an independent copy `X̄ ∈ H` (`X̄ =ᵈ X` and `X̄` independent from `X`) such that
`aX + bX̄ =ᵈ √(a² + b²) X` for all `a, b ≥ 0`. Its law is determined by
`σ̄² = E[X²]` and `σ²_ = -E[-X²]` (Chapter II, Proposition 1.7 for existence; Proposition 1.10 and
Corollary 1.11 for uniqueness; Remark 3.4). -/
def IsGNormal (X : Ω → ℝ) : Prop :=
  X ∈ S.H ∧ ∃ X' : Ω → ℝ, X' ∈ S.H ∧ IdentDistrib S S X' X ∧ S.IndepFrom X' X ∧
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IdentDistrib S S (fun ω ↦ a * X ω + b * X' ω) (fun ω ↦ Real.sqrt (a ^ 2 + b ^ 2) * X ω)

private theorem isLocLip_id_real : IsLocLip (fun x : ℝ ↦ x) :=
  isLocLip_of_lipschitzWith (K := 1) LipschitzWith.id

private theorem isLocLip_neg_real : IsLocLip (fun x : ℝ ↦ -x) :=
  isLocLip_of_lipschitzWith (K := 1) (LipschitzWith.id.neg)

private theorem isLocLip_sum (s : ℝ) : IsLocLip (fun p : ℝ × ℝ ↦ s * (p.1 + p.2)) := by
  refine ⟨|s|, 0, fun x y ↦ ?_⟩
  have h1 : ‖x.1 - y.1‖ ≤ ‖x - y‖ := norm_fst_le (x - y)
  have h2 : ‖x.2 - y.2‖ ≤ ‖x - y‖ := norm_snd_le (x - y)
  rw [Real.norm_eq_abs] at h1 h2
  have : |s * (x.1 + x.2) - s * (y.1 + y.2)| ≤ |s| * (|x.1 - y.1| + |x.2 - y.2|) := by
    rw [show s * (x.1 + x.2) - s * (y.1 + y.2) = s * ((x.1 - y.1) + (x.2 - y.2)) by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg s)
  simp only [pow_zero]
  nlinarith [abs_nonneg s, norm_nonneg (x - y)]

/-- Key step of Remark II.1.5: for an independent copy `X̄` of `X` and `s = ±1`,
`E[s(X + X̄)] = 2 E[sX]`. -/
private theorem expectation_smul_add_copy {X X' : Ω → ℝ} (hX : X ∈ S.H) (hX' : X' ∈ S.H)
    (hd : IdentDistrib S S X' X) (hi : S.IndepFrom X' X) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    S.E (fun ω ↦ s * (X ω + X' ω)) = 2 * S.E (fun ω ↦ s * X ω) := by
  have hsX : ∀ Z : Ω → ℝ, Z ∈ S.H → (fun ω ↦ s * Z ω) ∈ S.H := by
    intro Z hZ
    rcases hs with rfl | rfl
    · simpa using hZ
    · simpa using S.comp_mem 1 ![Z] (fun i ↦ by fin_cases i; simpa) (fun x ↦ -x 0)
        (isLocLip_of_lipschitzWith (K := 1)
          ((LipschitzWith.eval (α := fun _ : Fin 1 ↦ ℝ) 0).neg))
  have hdist : S.E (fun ω ↦ s * X' ω) = S.E (fun ω ↦ s * X ω) := by
    rcases hs with rfl | rfl
    · simpa using hd _ isLocLip_id_real
    · simpa using hd _ isLocLip_neg_real
  have h := hi _ (isLocLip_sum s)
  simp only at h
  rw [h]
  have hin : ∀ ω, S.E (fun ω' ↦ s * (X ω + X' ω')) = s * X ω + S.E (fun ω ↦ s * X ω) := by
    intro ω
    have := S.expectation_const_add (hsX X' hX') (s * X ω)
    rw [← hdist, ← this]
    congr 1
    ext ω'
    ring
  simp_rw [hin]
  have := S.expectation_const_add (hsX X hX) (S.E fun ω ↦ s * X ω)
  rw [show (fun ω ↦ s * X ω + S.E fun ω ↦ s * X ω) =
      (fun ω ↦ (S.E fun ω ↦ s * X ω) + s * X ω) from funext fun _ ↦ add_comm _ _, this]
  ring

/-- Key step of Remark II.1.5: the G-normal scaling with `a = b = 1`. -/
private theorem expectation_smul_add_gnormal {X X' : Ω → ℝ} (hX : X ∈ S.H)
    (hsc : IdentDistrib S S (fun ω ↦ 1 * X ω + 1 * X' ω)
      (fun ω ↦ Real.sqrt (1 ^ 2 + 1 ^ 2) * X ω)) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    S.E (fun ω ↦ s * (X ω + X' ω)) = Real.sqrt 2 * S.E (fun ω ↦ s * X ω) := by
  have hsX : (fun ω ↦ s * X ω) ∈ S.H := by
    rcases hs with rfl | rfl
    · simpa using hX
    · simpa using S.comp_mem 1 ![X] (fun i ↦ by fin_cases i; simpa) (fun x ↦ -x 0)
        (isLocLip_of_lipschitzWith (K := 1)
          ((LipschitzWith.eval (α := fun _ : Fin 1 ↦ ℝ) 0).neg))
  have h : S.E (fun ω ↦ s * (X ω + X' ω)) = S.E (fun ω ↦ s * (Real.sqrt 2 * X ω)) := by
    have hφ : IsLocLip (fun x : ℝ ↦ s * x) := by
      rcases hs with rfl | rfl
      · simpa using isLocLip_id_real
      · simpa using isLocLip_neg_real
    have := hsc _ hφ
    norm_num at this
    simpa using this
  rw [h]
  have := S.pos_hom _ hsX (Real.sqrt 2) (Real.sqrt_nonneg 2)
  rw [← this]
  congr 1
  ext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **A G-normal random variable has zero upper mean** (S. Peng, arXiv:1002.4546v1, Chapter II,
Remark 1.5): if `X` is G-normally distributed then `E[X] = 0`. The proof compares
`E[X + X̄] = 2 E[X]` (independence and identical distribution of the copy) with
`E[X + X̄] = E[√2 X] = √2 E[X]` (the defining scaling with `a = b = 1`). -/
theorem IsGNormal.expectation_eq_zero {X : Ω → ℝ} (h : S.IsGNormal X) : S.E X = 0 := by
  obtain ⟨hX, X', hX', hd, hi, hsc⟩ := h
  have h1 := S.expectation_smul_add_copy hX hX' hd hi 1 (Or.inl rfl)
  have h2 := S.expectation_smul_add_gnormal hX (hsc 1 1 zero_le_one zero_le_one) 1 (Or.inl rfl)
  simp only [one_mul] at h1 h2
  have hlt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : (2 - Real.sqrt 2) * S.E X = 0 := by
    have hX : (fun ω ↦ X ω) = X := rfl
    rw [hX] at h1 h2
    linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact h

/-- **A G-normal random variable has zero lower mean** (S. Peng, arXiv:1002.4546v1, Chapter II,
Remark 1.5): if `X` is G-normally distributed then `E[-X] = 0`, so `X` has no mean
uncertainty. -/
theorem IsGNormal.expectation_neg_eq_zero {X : Ω → ℝ} (h : S.IsGNormal X) :
    S.E (fun ω ↦ -X ω) = 0 := by
  obtain ⟨hX, X', hX', hd, hi, hsc⟩ := h
  have h1 := S.expectation_smul_add_copy hX hX' hd hi (-1) (Or.inr rfl)
  have h2 := S.expectation_smul_add_gnormal hX (hsc 1 1 zero_le_one zero_le_one) (-1)
    (Or.inr rfl)
  simp only [neg_one_mul] at h1 h2
  have hlt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : (2 - Real.sqrt 2) * S.E (fun ω ↦ -X ω) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact h

end SublinearExpectationSpace

end MathlibExt.Probability.SublinearExpectation
