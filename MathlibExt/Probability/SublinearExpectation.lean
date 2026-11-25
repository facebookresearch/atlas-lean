/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Pi

/-!
# Sublinear expectations, their representation, and coherent risk measures

Peng's framework of probability under model uncertainty starts from an *expectation* rather
than a probability measure. A **sublinear expectation** on a linear space `H` of real functions
on `Ω` that contains the constants is a functional `E` that is monotone, preserves constants, is
subadditive and is positively homogeneous (S. Peng, *Nonlinear Expectations and Stochastic
Calculus under Uncertainty*, arXiv:1002.4546v1, 2010, Chapter I, Definition 1.1).

* `exists_linear_le_eq`, `isGreatest_linear_le`: every subadditive, positively homogeneous
  functional on a real vector space is the pointwise maximum of the linear functionals it
  dominates, the maximum being attained (Peng, Chapter I, Theorem 2.1, first part), by the
  Hahn–Banach extension theorem `exists_extension_of_le_sublinear`.
* `IsSublinearExpectation.exists_linearExpectation`, `IsSublinearExpectation.isGreatest`: for a
  sublinear expectation the dominated linear functionals are linear expectations (monotone and
  constant preserving) (Peng, Chapter I, Theorem 2.1, second part).
* `IsSublinearExpectation.isGreatest_finite`: on a finite set of scenarios, `E[X]` is the
  maximum of `∑ q(ω) X(ω)` over a set of probability vectors `q` (Huber's finite-`Ω` case).
* `IsCoherentRiskMeasure`, `IsCoherentAcceptableSet`: Peng, Chapter I, Proposition 5.5 and
  Definition 5.1; `ρ(X) = E[-X]` is the bridge between the two notions (Peng, Chapter I, §5,
  following Proposition 5.5), and `{ρ ≤ 0}` is a coherent acceptable set (Exercise 5.6).
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.SublinearExpectation

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Positively homogeneous functionals vanish at zero.** If `E (c • x) = c * E x` for all
`c > 0`, then `E 0 = 0`. -/
theorem map_zero_of_posHom {E : V → ℝ} (hhom : ∀ c : ℝ, 0 < c → ∀ x, E (c • x) = c * E x) :
    E 0 = 0 := by
  have h := hhom 2 (by norm_num) 0
  rw [smul_zero] at h
  linarith

/-- **Representation of a sublinear functional, pointwise form.** Let `E` be a subadditive and
positively homogeneous functional on a real vector space. For every `x` there is a linear
functional `f ≤ E` with `f x = E x` (S. Peng, *Nonlinear Expectations and Stochastic Calculus under
Uncertainty*, arXiv:1002.4546v1, Chapter I, Theorem 2.1, first part; the proof is the
Hahn–Banach extension of `c • x ↦ c * E x` from the line through `x`). -/
theorem exists_linear_le_eq (E : V → ℝ) (hadd : ∀ x y, E (x + y) ≤ E x + E y)
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, E (c • x) = c * E x) (x : V) :
    ∃ f : V →ₗ[ℝ] ℝ, (∀ y, f y ≤ E y) ∧ f x = E x := by
  have h0 : E 0 = 0 := map_zero_of_posHom hhom
  -- `c * E x ≤ E (c • x)` for every real `c`.
  have hline : ∀ c : ℝ, c * E x ≤ E (c • x) := by
    intro c
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h1 := hadd (c • x) ((-c) • x)
      rw [← add_smul, add_neg_cancel, zero_smul, h0, hhom (-c) (by linarith) x] at h1
      linarith
    · simp [h0]
    · rw [hhom c hc x]
  have H : ∀ c : ℝ, c • x = 0 → c • E x = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · simp [h, h0]
  let f₀ : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (E x) H
  obtain ⟨g, hg, hgE⟩ := exists_extension_of_le_sublinear f₀ E hhom hadd (by
    rintro ⟨y, hy⟩
    have hy' : y ∈ ℝ ∙ x := by simpa [f₀, LinearPMap.domain_mkSpanSingleton] using hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have := LinearPMap.mkSpanSingleton'_apply x (E x) H c hy
    simp only [f₀, this, smul_eq_mul]
    exact hline c)
  refine ⟨g, hgE, ?_⟩
  have hx : x ∈ f₀.domain := by
    simp [f₀, LinearPMap.domain_mkSpanSingleton, Submodule.mem_span_singleton_self]
  rw [show x = ((⟨x, hx⟩ : f₀.domain) : V) from rfl, hg ⟨x, hx⟩]
  exact LinearPMap.mkSpanSingleton'_apply_self x (E x) H hx

/-- **Representation of a sublinear functional as a maximum of linear functionals.** A subadditive
and positively homogeneous functional `E` on a real vector space satisfies
`E x = max {f x : f linear, f ≤ E}` for every `x`, the maximum being attained (Peng,
arXiv:1002.4546v1, Chapter I, Theorem 2.1, first part). -/
theorem isGreatest_linear_le (E : V → ℝ) (hadd : ∀ x y, E (x + y) ≤ E x + E y)
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, E (c • x) = c * E x) (x : V) :
    IsGreatest {r | ∃ f : V →ₗ[ℝ] ℝ, (∀ y, f y ≤ E y) ∧ r = f x} (E x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, hfx⟩ := exists_linear_le_eq E hadd hhom x
    exact ⟨f, hf, hfx.symm⟩
  · rintro r ⟨f, hf, rfl⟩
    exact hf x

end Abstract

section Expectation

variable {Ω : Type*}

/-- **Sublinear expectation** (Peng, arXiv:1002.4546v1, Chapter I, Definition 1.1). `E` is a
sublinear expectation on the linear space `H` of real functions on `Ω` if `H` contains the
constants and `E` is monotone, constant preserving, subadditive and positively homogeneous on
`H`. The functional is total on `Ω → ℝ`, but only its values on `H` are constrained. (Peng also
assumes `|X| ∈ H` for `X ∈ H`; the results of this file do not need it.) -/
structure IsSublinearExpectation (H : Submodule ℝ (Ω → ℝ)) (E : (Ω → ℝ) → ℝ) : Prop where
  const_mem : ∀ c : ℝ, (fun _ : Ω ↦ c) ∈ H
  mono : ∀ X ∈ H, ∀ Y ∈ H, Y ≤ X → E Y ≤ E X
  const : ∀ c : ℝ, E (fun _ ↦ c) = c
  subadd : ∀ X ∈ H, ∀ Y ∈ H, E (X + Y) ≤ E X + E Y
  pos_hom : ∀ X ∈ H, ∀ c : ℝ, 0 ≤ c → E (c • X) = c * E X

variable {H : Submodule ℝ (Ω → ℝ)} {E : (Ω → ℝ) → ℝ}

/-- **Representation of a sublinear expectation, pointwise form.** If `E` is a sublinear
expectation on `H`, then for every `X ∈ H` there is a linear functional `f` on `H` with `f ≤ E`
and `f X = E X`, and every such dominated linear functional is a *linear expectation*: monotone
and constant preserving (Peng, arXiv:1002.4546v1, Chapter I, Theorem 2.1). The linear
expectations obtained this way are in general only finitely additive (Remark 2.2 there). -/
theorem IsSublinearExpectation.exists_linearExpectation (hE : IsSublinearExpectation H E)
    {X : Ω → ℝ} (hX : X ∈ H) :
    ∃ f : H →ₗ[ℝ] ℝ, (∀ Y : H, f Y ≤ E Y) ∧ f ⟨X, hX⟩ = E X ∧
      (∀ Y Z : H, (Y : Ω → ℝ) ≤ Z → f Y ≤ f Z) ∧ ∀ c : ℝ, f ⟨_, hE.const_mem c⟩ = c := by
  obtain ⟨f, hf, hfX⟩ := exists_linear_le_eq (fun Y : H ↦ E Y)
    (fun Y Z ↦ hE.subadd Y Y.2 Z Z.2)
    (fun c hc Y ↦ hE.pos_hom Y Y.2 c hc.le) ⟨X, hX⟩
  refine ⟨f, hf, hfX, ?_, ?_⟩
  · intro Y Z hYZ
    have h1 : f (Y - Z) ≤ E ((Y - Z : H) : Ω → ℝ) := hf (Y - Z)
    have h2 : E ((Y - Z : H) : Ω → ℝ) ≤ E (fun _ ↦ (0 : ℝ)) :=
      hE.mono _ (hE.const_mem 0) _ (Y - Z).2 (fun ω ↦ by
        simpa [sub_nonpos] using hYZ ω)
    rw [hE.const] at h2
    rw [map_sub] at h1
    linarith
  · intro c
    have h1 := hf ⟨_, hE.const_mem c⟩
    have h2 := hf ⟨_, hE.const_mem (-c)⟩
    have hneg : (⟨_, hE.const_mem (-c)⟩ : H) = -⟨_, hE.const_mem c⟩ := by
      ext ω; simp
    simp only [hE.const] at h1 h2
    rw [hneg, map_neg] at h2
    linarith

/-- **Representation of a sublinear expectation as a maximum of linear expectations.** For a
sublinear expectation `E` on `H` and `X ∈ H`, `E[X]` is the largest value of `f X` over the
linear expectations `f` on `H` (monotone, constant preserving) dominated by `E`, and the maximum
is attained: `E[X] = max_θ E_θ[X]` (Peng, arXiv:1002.4546v1, Chapter I, Theorem 2.1). -/
theorem IsSublinearExpectation.isGreatest (hE : IsSublinearExpectation H E) {X : Ω → ℝ}
    (hX : X ∈ H) :
    IsGreatest {r | ∃ f : H →ₗ[ℝ] ℝ, (∀ Y : H, f Y ≤ E Y) ∧
      (∀ Y Z : H, (Y : Ω → ℝ) ≤ Z → f Y ≤ f Z) ∧ (∀ c : ℝ, f ⟨_, hE.const_mem c⟩ = c) ∧
        r = f ⟨X, hX⟩} (E X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, hfX, hmono, hconst⟩ := hE.exists_linearExpectation hX
    exact ⟨f, hf, hmono, hconst, hfX.symm⟩
  · rintro r ⟨f, hf, -, -, rfl⟩
    exact hf ⟨X, hX⟩

/-- **Representation on a finite scenario set.** If `Ω` is finite and `E` is a sublinear
expectation on all functions `Ω → ℝ`, then
`E[X] = max {∑_ω q(ω) X(ω) : q ∈ Q}`, where `Q` is the set of probability vectors `q` with
`∑_ω q(ω) Y(ω) ≤ E[Y]` for every `Y`; the maximum is attained. This is the finite-`Ω` case of
Peng, arXiv:1002.4546v1, Chapter I, Theorem 2.1, which the Notes to Chapter I attribute to
Huber (*Robust Statistics*, 1981). -/
theorem IsSublinearExpectation.isGreatest_finite [Fintype Ω]
    (hE : IsSublinearExpectation ⊤ E) (X : Ω → ℝ) :
    IsGreatest {r | ∃ q : Ω → ℝ, (∀ ω, 0 ≤ q ω) ∧ ∑ ω, q ω = 1 ∧
      (∀ Y : Ω → ℝ, ∑ ω, q ω * Y ω ≤ E Y) ∧ r = ∑ ω, q ω * X ω} (E X) := by
  classical
  -- A linear functional on `Ω → ℝ`, through `H = ⊤`, is a weighted sum.
  have hsum : ∀ (f : (⊤ : Submodule ℝ (Ω → ℝ)) →ₗ[ℝ] ℝ) (Y : Ω → ℝ),
      f ⟨Y, Submodule.mem_top⟩ = ∑ ω, f ⟨Pi.single ω 1, Submodule.mem_top⟩ * Y ω := by
    intro f Y
    have hY : (⟨Y, Submodule.mem_top⟩ : (⊤ : Submodule ℝ (Ω → ℝ))) =
        ∑ ω, Y ω • ⟨Pi.single ω 1, Submodule.mem_top⟩ := by
      ext ω'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hY, map_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, hfX, hmono, hconst⟩ := hE.exists_linearExpectation (X := X) Submodule.mem_top
    refine ⟨fun ω ↦ f ⟨Pi.single ω 1, Submodule.mem_top⟩, ?_, ?_, ?_, ?_⟩
    · intro ω
      have h := hmono ⟨_, hE.const_mem 0⟩ ⟨Pi.single ω 1, Submodule.mem_top⟩ (fun ω' ↦ by
        by_cases h : ω' = ω
        · subst h; simp
        · simp [h])
      rwa [hconst] at h
    · have h := hsum f (fun _ ↦ 1)
      simp only [mul_one] at h
      rw [← h]
      exact hconst 1
    · intro Y
      rw [← hsum f Y]
      exact hf _
    · rw [← hsum f X]
      exact hfX.symm
  · rintro r ⟨q, -, -, hq, rfl⟩
    exact hq X

end Expectation

section RiskMeasure

variable {Ω : Type*} {H : Submodule ℝ (Ω → ℝ)}

/-- **Coherent risk measure** (after Artzner, Delbaen, Eber and Heath, 1999). A functional `ρ` on
the space `H` of risk positions (containing the constants) is a coherent risk measure if it is
antitone, satisfies `ρ(1) = -ρ(-1) = -1`, and is subadditive and positively homogeneous on `H`.
These are the four properties that Peng, arXiv:1002.4546v1, Chapter I, Proposition 5.5 proves for
the risk measure `ρ_A(X) = inf {m : m + X ∈ A}` of a coherent acceptable set `A`
(Definition 5.4). -/
structure IsCoherentRiskMeasure (H : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop where
  const_mem : ∀ c : ℝ, (fun _ : Ω ↦ c) ∈ H
  anti : ∀ X ∈ H, ∀ Y ∈ H, Y ≤ X → ρ X ≤ ρ Y
  one : ρ (fun _ ↦ 1) = -1
  neg_one : ρ (fun _ ↦ -1) = 1
  subadd : ∀ X ∈ H, ∀ Y ∈ H, ρ (X + Y) ≤ ρ X + ρ Y
  pos_hom : ∀ X ∈ H, ∀ c : ℝ, 0 ≤ c → ρ (c • X) = c * ρ X

/-- **Coherent acceptable set** (Peng, arXiv:1002.4546v1, Chapter I, Definition 5.1). A set `A`
of positions in `H` is a coherent acceptable set if it is upward closed in `H`, contains `0` but
not `-1`, and is closed under multiplication by nonnegative scalars and under convex
combinations. -/
structure IsCoherentAcceptableSet (H : Submodule ℝ (Ω → ℝ)) (A : Set (Ω → ℝ)) : Prop where
  subset : A ⊆ H
  mono : ∀ X ∈ A, ∀ Y ∈ H, X ≤ Y → Y ∈ A
  zero_mem : (0 : Ω → ℝ) ∈ A
  neg_one_not_mem : (fun _ : Ω ↦ (-1 : ℝ)) ∉ A
  smul_mem : ∀ X ∈ A, ∀ c : ℝ, 0 ≤ c → c • X ∈ A
  convex : ∀ X ∈ A, ∀ Y ∈ A, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • X + (1 - a) • Y ∈ A

/-- **Coherent risk measures of constants.** A coherent risk measure satisfies `ρ(c) = -c` for
every constant `c`, from `ρ(1) = -ρ(-1) = -1` and positive homogeneity. -/
theorem IsCoherentRiskMeasure.map_const {ρ : (Ω → ℝ) → ℝ} (hρ : IsCoherentRiskMeasure H ρ)
    (c : ℝ) : ρ (fun _ ↦ c) = -c := by
  rcases le_total 0 c with hc | hc
  · have h := hρ.pos_hom _ (hρ.const_mem 1) c hc
    have heq : (c • fun _ : Ω ↦ (1 : ℝ)) = fun _ ↦ c := by ext; simp
    rw [heq, hρ.one] at h
    linarith
  · have h := hρ.pos_hom _ (hρ.const_mem (-1)) (-c) (by linarith)
    have heq : ((-c) • fun _ : Ω ↦ (-1 : ℝ)) = fun _ ↦ c := by ext; simp
    rw [heq, hρ.neg_one] at h
    linarith

/-- **Sublinear expectations give coherent risk measures.** If `E` is a sublinear expectation on
`H`, then `ρ(X) = E[-X]` is a coherent risk measure (Peng, arXiv:1002.4546v1, Chapter I, §5, the
remark following Proposition 5.5). -/
theorem IsSublinearExpectation.isCoherentRiskMeasure {E : (Ω → ℝ) → ℝ}
    (hE : IsSublinearExpectation H E) : IsCoherentRiskMeasure H (fun X ↦ E (-X)) where
  const_mem := hE.const_mem
  anti X hX Y hY hYX := hE.mono _ (H.neg_mem hY) _ (H.neg_mem hX) (fun ω ↦ neg_le_neg (hYX ω))
  one := by
    have : (-fun _ : Ω ↦ (1 : ℝ)) = fun _ ↦ -1 := by ext; simp
    simp only [this, hE.const]
  neg_one := by
    have : (-fun _ : Ω ↦ (-1 : ℝ)) = fun _ ↦ 1 := by ext; simp
    simp only [this, hE.const]
  subadd X hX Y hY := by
    rw [neg_add]
    exact hE.subadd _ (H.neg_mem hX) _ (H.neg_mem hY)
  pos_hom X hX c hc := by
    rw [← smul_neg]
    exact hE.pos_hom _ (H.neg_mem hX) c hc

/-- **Coherent risk measures give sublinear expectations.** If `ρ` is a coherent risk measure on
`H`, then `E[X] = ρ(-X)` is a sublinear expectation (Peng, arXiv:1002.4546v1, Chapter I, §5, the
remark following Proposition 5.5). -/
theorem IsCoherentRiskMeasure.isSublinearExpectation {ρ : (Ω → ℝ) → ℝ}
    (hρ : IsCoherentRiskMeasure H ρ) : IsSublinearExpectation H (fun X ↦ ρ (-X)) where
  const_mem := hρ.const_mem
  mono X hX Y hY hYX := hρ.anti _ (H.neg_mem hY) _ (H.neg_mem hX) (fun ω ↦ neg_le_neg (hYX ω))
  const c := by
    have : (-fun _ : Ω ↦ c) = fun _ ↦ -c := by ext; simp
    rw [this, hρ.map_const, neg_neg]
  subadd X hX Y hY := by
    rw [neg_add]
    exact hρ.subadd _ (H.neg_mem hX) _ (H.neg_mem hY)
  pos_hom X hX c hc := by
    rw [← smul_neg]
    exact hρ.pos_hom _ (H.neg_mem hX) c hc

/-- **The acceptance set of a coherent risk measure.** If `ρ` is a coherent risk measure on `H`,
then `A_ρ = {X ∈ H : ρ(X) ≤ 0}` is a coherent acceptable set (Peng, arXiv:1002.4546v1, Chapter I,
Exercise 5.6). -/
theorem IsCoherentRiskMeasure.isCoherentAcceptableSet {ρ : (Ω → ℝ) → ℝ}
    (hρ : IsCoherentRiskMeasure H ρ) : IsCoherentAcceptableSet H {X | X ∈ H ∧ ρ X ≤ 0} where
  subset _ hX := hX.1
  mono X hX Y hY hXY := ⟨hY, (hρ.anti _ hY _ hX.1 hXY).trans hX.2⟩
  zero_mem := by
    refine ⟨H.zero_mem, ?_⟩
    have h := hρ.map_const 0
    have h0 : (fun _ : Ω ↦ (0 : ℝ)) = 0 := rfl
    rw [h0] at h
    rw [h, neg_zero]
  neg_one_not_mem := by
    rintro ⟨-, h⟩
    rw [hρ.neg_one] at h
    linarith
  smul_mem X hX c hc := ⟨H.smul_mem c hX.1, by
    rw [hρ.pos_hom X hX.1 c hc]
    exact mul_nonpos_of_nonneg_of_nonpos hc hX.2⟩
  convex X hX Y hY a ha0 ha1 := by
    refine ⟨H.add_mem (H.smul_mem a hX.1) (H.smul_mem (1 - a) hY.1), ?_⟩
    have h := hρ.subadd _ (H.smul_mem a hX.1) _ (H.smul_mem (1 - a) hY.1)
    rw [hρ.pos_hom X hX.1 a ha0, hρ.pos_hom Y hY.1 (1 - a) (by linarith)] at h
    have h1 : a * ρ X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hX.2
    have h2 : (1 - a) * ρ Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hY.2
    linarith

end RiskMeasure

end MathlibExt.Probability.SublinearExpectation
