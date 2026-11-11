/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-!
# Kimura two-parameter (K80) transition probabilities, distance and identifiability

**Model (frozen).** Nucleotides are indexed `0 = A`, `1 = C`, `2 = G`, `3 = T`, as in
`SubstitutionModels`, so a substitution is a *transition* (`A ↔ G`, `C ↔ T`) exactly when the
indices have the same parity. In Kimura's (1980) two-parameter model each base mutates to its
transition partner at rate `α` and to *each* of its two transversion partners at rate `β`, so
the total substitution rate out of every base is `α + 2β` (Felsenstein 2004, chapter 13). The
repository's generator `k80Rate κ` is the unnormalized case `α = κ / 4`, `β = 1 / 4`
(entries in `k80Rate_apply`); a general model with `β > 0` is `(4β) • k80Rate (α / β)`. Over a
path of length `t` the transition matrix `exp (t • Q)` depends on the rates and time only
through the composite parameters `a = α t` and `b = β t`, and equals `kimuraProb a b`:

* `1/4 + 1/4 · e^{-4b} + 1/2 · e^{-2(a + b)}` on the diagonal,
* `P = 1/4 + 1/4 · e^{-4b} - 1/2 · e^{-2(a + b)}` for the transition,
* `1/4 - 1/4 · e^{-4b}` for each transversion, so `Q = 1/2 - 1/2 · e^{-4b}` in total.

Kimura states these for two sequences that diverged `T` time units ago, i.e. for the path
length `t = 2T` between them; we state them per path length.

**Distance and identifiability.** The proportions satisfy `1 - 2Q = e^{-4b}` and
`1 - 2P - Q = e^{-2(a + b)}`, so on the domain `1 - 2Q > 0`, `1 - 2P - Q > 0` they determine
`b = -(1/4) · log (1 - 2Q)` and `a = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)`, and
the **Kimura distance** `d = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q) = a + 2b` is the
expected number of substitutions per site `(α + 2β) t`. The map `(a, b) ↦ (P, Q)` is a
bijection from `ℝ × ℝ` onto this domain. The boundary `1 - 2Q = 0` or `1 - 2P - Q = 0`
(saturation) is excluded: there the distance diverges and Lean's `log 0 = 0` gives junk.

The separate values of `α`, `β` and `t` are **not** identifiable: rescaling all rates by `c`
and time by `1 / c` leaves the matrix unchanged (`ctmcTransition_smul_k80Rate_eq_iff`). Fixing
the normalization `β = 1/4` of `k80Rate` identifies `t` and `κ t`
(`ctmcTransition_k80Rate_eq_iff`).

The algebraic identities hold for all real parameters; the stochastic reading needs
`a, b ≥ 0` (`kimuraProb_nonneg`).

## Main definitions

* `kimuraProb a b`: the closed-form K80 transition matrix in the composite parameters.
* `transitionProp M i`, `transversionProp M i`: Kimura's `P` and `Q` in row `i` of `M`.
* `kimuraDistance P Q`, `kimuraTransitionParam P Q`, `kimuraTransversionParam Q`.

## Main results

* `ctmcTransition_k80Rate`, `ctmcTransition_smul_k80Rate`: `exp (t • Q)` in closed form,
  by diagonalizing `k80Rate κ` (eigenvalues `0`, `-1`, `-(κ + 1)/2` twice).
* `sum_kimuraProb`, `kimuraProb_zero`, `kimuraProb_nonneg`: stochasticity, identity at `0`.
* `transitionProp_kimuraProb`, `transversionProp_kimuraProb`: the proportions `P`, `Q`.
* `kimuraTransitionParam_kimuraProb`, `kimuraTransversionParam_kimuraProb`,
  `kimuraDistance_kimuraProb`, `kimuraDistance_k80Rate`: recovery of `a`, `b` and `d`.
* `kimuraProb_injective`, `transitionProp_kimuraProb_recover`,
  `transversionProp_kimuraProb_recover`: `(a, b) ↔ (P, Q)` is a bijection onto the domain.
* `ctmcTransition_smul_k80Rate_eq_iff`, `ctmcTransition_k80Rate_eq_iff`: exactly the
  composite parameters are identifiable.
* `kimuraProb_jukesCantor`, `kimuraDistance_jukesCantor`, `ctmcTransition_k80Rate_one`: the
  case `α = β` is `JukesCantor.jcProb`, and the Kimura distance is `JukesCantor.jcDistance`.

## References

* M. Kimura, *A simple method for estimating evolutionary rates of base substitutions through
  comparative studies of nucleotide sequences*, J. Mol. Evol. 16 (1980), 111–120.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 13.
-/

@[expose] public section

open Real Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.JukesCantor

namespace MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-- The entries of the K80 rate matrix: `-(κ + 2) / 4` on the diagonal, `κ / 4` for a transition
(indices of equal parity) and `1 / 4` for a transversion. -/
theorem k80Rate_apply (κ : ℝ) (i j : Fin 4) :
    k80Rate κ i j =
      if i = j then -(κ + 2) / 4 else if (i : ℕ) % 2 = (j : ℕ) % 2 then κ / 4 else 1 / 4 := by
  fin_cases i <;> fin_cases j <;>
    simp [k80Rate, hkyRate, gtrRate, hkyExchangeability, sum_erase_eq_sub, Fin.sum_univ_four] <;>
    ring

/-- An eigenbasis of the K80 rate matrix, as columns (order `A, C, G, T`): the constant vector
(eigenvalue `0`), the purine/pyrimidine contrast (eigenvalue `-1`), and the contrasts within the
purines and within the pyrimidines (eigenvalue `-(κ + 1) / 2`). -/
def k80Eigenbasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 0; 1, -1, 0, 1; 1, 1, -1, 0; 1, -1, 0, -1]

/-- The K80 eigenbasis as a unit, with its explicit inverse. -/
noncomputable def k80EigenbasisUnit : (Matrix (Fin 4) (Fin 4) ℝ)ˣ where
  val := k80Eigenbasis
  inv := !![1/4, 1/4, 1/4, 1/4; 1/4, -1/4, 1/4, -1/4; 1/2, 0, -1/2, 0; 0, 1/2, 0, -1/2]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k80Eigenbasis, mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k80Eigenbasis, mul_apply, Fin.sum_univ_four]

/-- Diagonalization of `t • k80Rate κ`. -/
theorem smul_k80Rate_eq (κ t : ℝ) :
    t • k80Rate κ =
      (k80EigenbasisUnit : Matrix (Fin 4) (Fin 4) ℝ) *
        diagonal ![0, -t, -((κ + 1) * t / 2), -((κ + 1) * t / 2)] *
        (↑k80EigenbasisUnit⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [k80EigenbasisUnit, Units.inv_mk, Units.val_mk, Matrix.smul_apply, k80Rate_apply,
    mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num [k80Eigenbasis] <;> ring

/-- The **Kimura two-parameter transition matrix** in terms of the composite parameters
`a = α t` (transition rate times time) and `b = β t` (rate of each of the two transversions
times time), in the order `A, C, G, T`:

* `1/4 + 1/4 · e^{-4b} + 1/2 · e^{-2(a + b)}` on the diagonal,
* `1/4 + 1/4 · e^{-4b} - 1/2 · e^{-2(a + b)}` for a transition (`A ↔ G`, `C ↔ T`),
* `1/4 - 1/4 · e^{-4b}` for each transversion.

These are the formulas of Kimura (1980), eqs. (5)–(6). -/
noncomputable def kimuraProb (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i = j then 1 / 4 + 1 / 4 * exp (-4 * b) + 1 / 2 * exp (-2 * (a + b))
    else if (i : ℕ) % 2 = (j : ℕ) % 2 then
      1 / 4 + 1 / 4 * exp (-4 * b) - 1 / 2 * exp (-2 * (a + b))
    else 1 / 4 - 1 / 4 * exp (-4 * b)

/-- **K80 transition probabilities in closed form**: the transition function of `k80Rate κ`
(transition rate `α = κ / 4`, transversion rate `β = 1 / 4`) over time `t` is
`kimuraProb (κ t / 4) (t / 4)`, for all real `κ` and `t`. -/
theorem ctmcTransition_k80Rate (κ t : ℝ) :
    ctmcTransition (k80Rate κ) t = kimuraProb (κ * t / 4) (t / 4) := by
  have h1 : -4 * (t / 4) = -t := by ring
  have h2 : -2 * (κ * t / 4 + t / 4) = -((κ + 1) * t / 2) := by ring
  ext i j
  rw [ctmcTransition, smul_k80Rate_eq, Matrix.exp_units_conj, Matrix.exp_diagonal]
  simp only [kimuraProb, of_apply, h1, h2, k80EigenbasisUnit, Units.inv_mk, Units.val_mk,
    mul_apply, Fin.sum_univ_four, Pi.exp_def]
  fin_cases i <;> fin_cases j <;> norm_num [k80Eigenbasis, ← Real.exp_eq_exp_ℝ] <;> ring

/-- Each row of the Kimura transition matrix sums to `1`, for all real `a`, `b`. -/
theorem sum_kimuraProb (a b : ℝ) (i : Fin 4) : ∑ j, kimuraProb a b i j = 1 := by
  fin_cases i <;> simp [kimuraProb, Fin.sum_univ_four] <;> ring

/-- At `a = b = 0` (time `0`) the Kimura transition matrix is the identity. -/
theorem kimuraProb_zero : kimuraProb 0 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [kimuraProb]; norm_num
  · simp only [kimuraProb, of_apply, h, ite_false, one_apply_ne h]
    split_ifs <;> norm_num

/-- For `0 ≤ a` and `0 ≤ b` every entry of the Kimura matrix is nonnegative. The transition
entry is the delicate one: with `z = e^{-2b}` it is at least `(1 - z)² / 4`. -/
theorem kimuraProb_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : Fin 4) :
    0 ≤ kimuraProb a b i j := by
  have hz : exp (-4 * b) = exp (-2 * b) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have hy : exp (-2 * (a + b)) ≤ exp (-2 * b) := exp_le_exp.mpr (by linarith)
  have hz1 : exp (-2 * b) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hx1 : exp (-4 * b) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have := exp_pos (-4 * b)
  have := exp_pos (-2 * (a + b))
  unfold kimuraProb
  simp only [of_apply]
  split_ifs
  · positivity
  · rw [hz]; nlinarith [sq_nonneg (1 - exp (-2 * b))]
  · linarith

/-! ## Transition and transversion proportions -/

/-- The proportion of **transition differences** in row `i` of a nucleotide matrix `M`: the
entry `M i j` for the base `j ≠ i` of the same class (purine/pyrimidine), Kimura's `P`. -/
noncomputable def transitionProp (M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin 4 => j ≠ i ∧ (j : ℕ) % 2 = (i : ℕ) % 2), M i j

/-- The proportion of **transversion differences** in row `i` of a nucleotide matrix `M`: the
total of `M i j` over the two bases `j` of the other class, Kimura's `Q`. -/
noncomputable def transversionProp (M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin 4 => (j : ℕ) % 2 ≠ (i : ℕ) % 2), M i j

/-- Transitions and transversions together are all the differences:
`P + Q = ∑_{j ≠ i} M i j`. -/
theorem transitionProp_add_transversionProp (M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) :
    transitionProp M i + transversionProp M i = ∑ j ∈ univ.erase i, M i j := by
  fin_cases i <;>
    simp [transitionProp, transversionProp, sum_filter, Fin.sum_univ_four, sum_erase_eq_sub] <;>
    ring

/-- The transition proportion of the Kimura matrix, `P = 1/4 + 1/4 · e^{-4b} - 1/2 · e^{-2(a+b)}`,
whatever the starting base. -/
theorem transitionProp_kimuraProb (a b : ℝ) (i : Fin 4) :
    transitionProp (kimuraProb a b) i =
      1 / 4 + 1 / 4 * exp (-4 * b) - 1 / 2 * exp (-2 * (a + b)) := by
  fin_cases i <;> simp [transitionProp, kimuraProb, sum_filter, Fin.sum_univ_four]

/-- The transversion proportion of the Kimura matrix, `Q = 1/2 - 1/2 · e^{-4b}`, whatever the
starting base. -/
theorem transversionProp_kimuraProb (a b : ℝ) (i : Fin 4) :
    transversionProp (kimuraProb a b) i = 1 / 2 - 1 / 2 * exp (-4 * b) := by
  fin_cases i <;> simp [transversionProp, kimuraProb, sum_filter, Fin.sum_univ_four] <;> ring

/-- In the Kimura matrix, `1 - 2Q = e^{-4b}`. -/
theorem one_sub_two_mul_transversionProp_kimuraProb (a b : ℝ) (i : Fin 4) :
    1 - 2 * transversionProp (kimuraProb a b) i = exp (-4 * b) := by
  rw [transversionProp_kimuraProb]; ring

/-- In the Kimura matrix, `1 - 2P - Q = e^{-2(a + b)}`. -/
theorem one_sub_two_mul_transitionProp_sub_transversionProp_kimuraProb (a b : ℝ) (i : Fin 4) :
    1 - 2 * transitionProp (kimuraProb a b) i - transversionProp (kimuraProb a b) i =
      exp (-2 * (a + b)) := by
  rw [transitionProp_kimuraProb, transversionProp_kimuraProb]; ring

/-! ## Recovery of the composite parameters and the Kimura distance -/

/-- The transversion parameter recovered from a transversion proportion `Q`:
`b = -(1/4) · log (1 - 2Q)`. Meaningful on the domain `1 - 2Q > 0`; elsewhere it is Lean's
totalized logarithm. -/
noncomputable def kimuraTransversionParam (Q : ℝ) : ℝ :=
  -(1 / 4) * log (1 - 2 * Q)

/-- The transition parameter recovered from proportions `P`, `Q`:
`a = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)`. Meaningful on the domain
`1 - 2P - Q > 0`, `1 - 2Q > 0`. -/
noncomputable def kimuraTransitionParam (P Q : ℝ) : ℝ :=
  -(1 / 2) * log (1 - 2 * P - Q) + 1 / 4 * log (1 - 2 * Q)

/-- The **Kimura two-parameter distance** (Kimura 1980) from the proportions `P` of transition
and `Q` of transversion differences: `d = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)`.
It is the expected number of substitutions per site on the domain `1 - 2P - Q > 0`,
`1 - 2Q > 0`; it diverges at the boundary, where the totalized logarithm returns junk. -/
noncomputable def kimuraDistance (P Q : ℝ) : ℝ :=
  -(1 / 2) * log (1 - 2 * P - Q) - 1 / 4 * log (1 - 2 * Q)

/-- The distance splits as `d = a + 2b`: one transition and two transversion classes. -/
theorem kimuraDistance_eq (P Q : ℝ) :
    kimuraDistance P Q = kimuraTransitionParam P Q + 2 * kimuraTransversionParam Q := by
  unfold kimuraDistance kimuraTransitionParam kimuraTransversionParam; ring

/-- **Recovery of `b`**: the transversion proportion of `kimuraProb a b` determines `b`. -/
theorem kimuraTransversionParam_kimuraProb (a b : ℝ) (i : Fin 4) :
    kimuraTransversionParam (transversionProp (kimuraProb a b) i) = b := by
  rw [kimuraTransversionParam, one_sub_two_mul_transversionProp_kimuraProb, log_exp]; ring

/-- **Recovery of `a`**: the transition and transversion proportions of `kimuraProb a b`
determine `a`. -/
theorem kimuraTransitionParam_kimuraProb (a b : ℝ) (i : Fin 4) :
    kimuraTransitionParam (transitionProp (kimuraProb a b) i)
      (transversionProp (kimuraProb a b) i) = a := by
  rw [kimuraTransitionParam, one_sub_two_mul_transitionProp_sub_transversionProp_kimuraProb,
    one_sub_two_mul_transversionProp_kimuraProb, log_exp, log_exp]; ring

/-- **Kimura distance recovery**: from the proportions of `kimuraProb a b` the Kimura distance
returns `a + 2b`, i.e. `(α + 2β) t`, the expected number of substitutions per site. -/
theorem kimuraDistance_kimuraProb (a b : ℝ) (i : Fin 4) :
    kimuraDistance (transitionProp (kimuraProb a b) i) (transversionProp (kimuraProb a b) i) =
      a + 2 * b := by
  rw [kimuraDistance_eq, kimuraTransitionParam_kimuraProb, kimuraTransversionParam_kimuraProb]

/-- **Identifiability of the composite parameters**: the Kimura transition matrix determines
`(a, b) = (α t, β t)`, for all real `a`, `b`. -/
theorem kimuraProb_injective :
    Function.Injective fun ab : ℝ × ℝ => kimuraProb ab.1 ab.2 := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  simp only at h
  have hb := kimuraTransversionParam_kimuraProb a₁ b₁ 0
  have ha := kimuraTransitionParam_kimuraProb a₁ b₁ 0
  rw [h, kimuraTransversionParam_kimuraProb] at hb
  rw [h, kimuraTransitionParam_kimuraProb] at ha
  rw [ha, hb]

/-- **Every point of the domain is attained**, transversion part: if `1 - 2Q > 0`, the
recovered parameters reproduce the transversion proportion `Q` (whatever `P`). -/
theorem transversionProp_kimuraProb_recover {P Q : ℝ} (hQ : 0 < 1 - 2 * Q) (i : Fin 4) :
    transversionProp (kimuraProb (kimuraTransitionParam P Q) (kimuraTransversionParam Q)) i =
      Q := by
  rw [transversionProp_kimuraProb, kimuraTransversionParam,
    show -4 * (-(1 / 4) * log (1 - 2 * Q)) = log (1 - 2 * Q) by ring, exp_log hQ]
  ring

/-- **Every point of the domain is attained**: if `1 - 2Q > 0` and `1 - 2P - Q > 0`, the
recovered parameters reproduce the transition proportion `P`. Together with
`transversionProp_kimuraProb_recover` and the recovery theorems, `(a, b) ↦ (P, Q)` is a
bijection from `ℝ × ℝ` onto this domain. -/
theorem transitionProp_kimuraProb_recover {P Q : ℝ} (hQ : 0 < 1 - 2 * Q)
    (hPQ : 0 < 1 - 2 * P - Q) (i : Fin 4) :
    transitionProp (kimuraProb (kimuraTransitionParam P Q) (kimuraTransversionParam Q)) i =
      P := by
  rw [transitionProp_kimuraProb, kimuraTransitionParam, kimuraTransversionParam,
    show -4 * (-(1 / 4) * log (1 - 2 * Q)) = log (1 - 2 * Q) by ring,
    show -2 * (-(1 / 2) * log (1 - 2 * P - Q) + 1 / 4 * log (1 - 2 * Q) +
      -(1 / 4) * log (1 - 2 * Q)) = log (1 - 2 * P - Q) by ring, exp_log hQ, exp_log hPQ]
  ring

/-! ## The K80 model: what the transition matrix identifies -/

/-- The K80 model with an overall rate `c`, `c • k80Rate κ`, has transition rate `α = c κ / 4`
and transversion rate `β = c / 4`; its transition function over time `t` is
`kimuraProb (α t) (β t)`. -/
theorem ctmcTransition_smul_k80Rate (c κ t : ℝ) :
    ctmcTransition (c • k80Rate κ) t = kimuraProb (c * κ * t / 4) (c * t / 4) := by
  rw [ctmcTransition_smul, ctmcTransition_k80Rate]
  congr 1
  ring

/-- **Only the composite parameters are identifiable**: two rate-scaled K80 models give the
same transition matrix exactly when they have the same `β t = c t / 4` and `α t = c κ t / 4`.
In particular the rate scale `c` and the time `t` enter only through their product. -/
theorem ctmcTransition_smul_k80Rate_eq_iff {c₁ κ₁ t₁ c₂ κ₂ t₂ : ℝ} :
    ctmcTransition (c₁ • k80Rate κ₁) t₁ = ctmcTransition (c₂ • k80Rate κ₂) t₂ ↔
      c₁ * t₁ = c₂ * t₂ ∧ c₁ * κ₁ * t₁ = c₂ * κ₂ * t₂ := by
  rw [ctmcTransition_smul_k80Rate, ctmcTransition_smul_k80Rate]
  constructor
  · intro h
    have h' := @kimuraProb_injective (_, _) (_, _) h
    simp only [Prod.mk.injEq] at h'
    constructor <;> linarith [h'.1, h'.2]
  · rintro ⟨h₁, h₂⟩
    congr 1 <;> linarith

/-- **Identifiability under the K80 normalization** (transversion rate `β = 1/4`): the
transition matrix of `k80Rate κ` over time `t` determines `t` and `κ t`, hence `κ` when
`t ≠ 0`. -/
theorem ctmcTransition_k80Rate_eq_iff {κ₁ t₁ κ₂ t₂ : ℝ} :
    ctmcTransition (k80Rate κ₁) t₁ = ctmcTransition (k80Rate κ₂) t₂ ↔
      t₁ = t₂ ∧ κ₁ * t₁ = κ₂ * t₂ := by
  simpa only [one_smul, one_mul] using
    ctmcTransition_smul_k80Rate_eq_iff (c₁ := 1) (κ₁ := κ₁) (t₁ := t₁) (c₂ := 1) (κ₂ := κ₂)
      (t₂ := t₂)

/-- **K80 distance recovery**: the Kimura distance of the transition and transversion
proportions of `k80Rate κ` over time `t` is `(κ + 2) t / 4`, the total substitution rate
`-k80Rate κ i i = (κ + 2) / 4` times `t`. -/
theorem kimuraDistance_k80Rate (κ t : ℝ) (i : Fin 4) :
    kimuraDistance (transitionProp (ctmcTransition (k80Rate κ) t) i)
        (transversionProp (ctmcTransition (k80Rate κ) t) i) = (κ + 2) / 4 * t := by
  rw [ctmcTransition_k80Rate, kimuraDistance_kimuraProb]; ring

/-! ## The Jukes–Cantor specialization `α = β` -/

/-- With equal transition and transversion parameters `a = b = μ t / 3`, the Kimura matrix is
the Jukes–Cantor transition matrix `jcProb μ t`. -/
theorem kimuraProb_jukesCantor (μ t : ℝ) :
    kimuraProb (μ * t / 3) (μ * t / 3) = Matrix.of (jcProb μ t) := by
  have h1 : -4 * (μ * t / 3) = -4 * μ * t / 3 := by ring
  have h2 : -2 * (μ * t / 3 + μ * t / 3) = -4 * μ * t / 3 := by ring
  ext i j
  simp only [kimuraProb, jcProb, of_apply, h1, h2]
  split_ifs <;> ring

/-- On Jukes–Cantor data the two Kimura proportions add up to the proportion of differing
sites `pDiff`. -/
theorem transitionProp_add_transversionProp_jcProb (μ t : ℝ) (i : Fin 4) :
    transitionProp (Matrix.of (jcProb μ t)) i + transversionProp (Matrix.of (jcProb μ t)) i =
      pDiff μ t i := by
  rw [transitionProp_add_transversionProp, pDiff]
  rfl

/-- **The Kimura distance reduces to the Jukes–Cantor distance** on Jukes–Cantor data:
`kimuraDistance P Q = jcDistance (P + Q)`, both equal to `μ t`. -/
theorem kimuraDistance_jukesCantor (μ t : ℝ) (i : Fin 4) :
    kimuraDistance (transitionProp (Matrix.of (jcProb μ t)) i)
        (transversionProp (Matrix.of (jcProb μ t)) i) =
      jcDistance (transitionProp (Matrix.of (jcProb μ t)) i +
        transversionProp (Matrix.of (jcProb μ t)) i) := by
  rw [transitionProp_add_transversionProp_jcProb, jcDistance_pDiff, ← kimuraProb_jukesCantor,
    kimuraDistance_kimuraProb]
  ring

/-- K80 with `κ = 1` has the Jukes–Cantor transition function with rate `μ = 3/4`, through
the existing `k80Rate_one` and `JukesCantor.jcProb_eq_exp`. -/
theorem ctmcTransition_k80Rate_one (t : ℝ) :
    ctmcTransition (k80Rate 1) t = Matrix.of (jcProb (3 / 4) t) := by
  ext i j
  rw [ctmcTransition, k80Rate_one, of_apply, jcProb_eq_exp]

end MathlibExt.Biology.Phylogenetics.SubstitutionModels
