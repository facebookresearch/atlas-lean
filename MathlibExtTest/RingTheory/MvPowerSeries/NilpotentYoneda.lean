/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.NilpotentYoneda

@[expose] public section

open MvPowerSeries

universe u v

/-- Consumer with the original binders: rings and algebras live in the
same universe `u`, the index type is finite, and the conclusion is phrased
with the explicit nilpotency and membership hypotheses. -/
private theorem exactSource
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C)
        (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J),
          t C J x = nilpotentEval J hJ x hx f :=
  MvPowerSeries.existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    t ht_nat

/-- Higher-universe consumer: the coefficient ring lives in `Type v`. -/
private theorem exactSourceUniverse
    {R : Type v} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type v) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type v) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type v) [CommRing C] [Algebra R C] (J : Ideal C)
        (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J),
          t C J x = nilpotentEval J hJ x hx f :=
  MvPowerSeries.existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    t ht_nat

/-- Boundary example: the constant-coefficient hypothesis in
`nilpotentEval_mem` matters. At the zero point of the zero ideal, the
series `1` evaluates to `1`, which does not lie in the zero ideal. -/
example : nilpotentEval (R := ℚ) (σ := Fin 1) (⊥ : Ideal ℚ) ⟨1, pow_one _⟩
    (fun _ => 0) (fun _ => by simp)
    ((1 : MvPolynomial (Fin 1) ℚ) : MvPowerSeries (Fin 1) ℚ) = 1 := by
  rw [nilpotentEval_coe (⊥ : Ideal ℚ) ⟨1, pow_one _⟩ (fun s => by simp)
    (1 : MvPolynomial (Fin 1) ℚ)]
  simp

/-- Consumer of the bridge to the adic evaluation: the existence and
uniqueness theorem also holds with `adicEval` in place of `nilpotentEval`. -/
private theorem existsUnique_apply_eq_adicEval
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C),
        IsNilpotent J → ∀ x : σ → C, (∀ s, x s ∈ J) →
          t C J x = adicEval J x f := by
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent t ht_nat
  refine ⟨f, fun C _ _ J hJ x hx =>
      (hf C J hJ x hx).trans (nilpotentEval_eq_adicEval J hJ hx f),
    fun g hg => huniq g fun C _ _ J hJ x hx =>
      (hg C J hJ x hx).trans (nilpotentEval_eq_adicEval J hJ hx g).symm⟩

/-! The coordinate rule `t C J x = x ()` in one variable. Its naturality holds by definition, and
the representation theorem identifies its unique representing series as `X ()`. -/

/-- Naturality of the coordinate rule `t C J x = x ()`, proved directly: an algebra map `φ` sends
the coordinate of `x` to the coordinate of `φ ∘ x`. -/
private theorem coordinate_natural (R : Type u) [CommRing R] :
    ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Unit → C, (∀ s, x s ∈ J) → (φ ∘ x) () = φ (x ()) := by
  intros
  rfl

/-- The series `X ()` represents the coordinate rule: at every point of a nilpotent ideal it
evaluates to the coordinate. -/
private theorem coordinate_eq_nilpotentEval_X {R : Type u} [CommRing R] (C : Type u)
    [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J) (x : Unit → C)
    (hx : ∀ s, x s ∈ J) : x () = nilpotentEval J hJ x hx (X () : MvPowerSeries Unit R) := by
  rw [← MvPolynomial.coe_X, nilpotentEval_coe, MvPolynomial.aeval_X]

/-- The representation theorem on the coordinate rule: a power series represents the rule exactly
when it is `X ()`. The forward direction is the uniqueness half of
`existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent`. -/
private theorem represents_coordinate_iff {R : Type u} [CommRing R] (f : MvPowerSeries Unit R) :
    (∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
      (x : Unit → C) (hx : ∀ s, x s ∈ J), x () = nilpotentEval J hJ x hx f) ↔ f = X () := by
  refine ⟨fun hf => (existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    (fun _ _ _ _ x => x ()) (coordinate_natural R)).unique hf coordinate_eq_nilpotentEval_X, ?_⟩
  rintro rfl
  exact coordinate_eq_nilpotentEval_X

/-- Over `ℤ`, the series `X () + X ()` does not represent the coordinate rule. -/
example : ¬ ∀ (C : Type) [CommRing C] [Algebra ℤ C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : Unit → C) (hx : ∀ s, x s ∈ J),
      x () = nilpotentEval J hJ x hx (X () + X () : MvPowerSeries Unit ℤ) := by
  intro h
  have h2 := congrArg (coeff (Finsupp.single () 1)) ((represents_coordinate_iff _).mp h)
  simp [coeff_X] at h2

/-- The `AlgHom` is `adicEvalAlgHom` at the nilpotent ideal. -/
example {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] {σ : Type*}
    [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) [IsAdicComplete J C]
    (x : σ → C) (hx : ∀ s, x s ∈ J) :
    nilpotentEvalAlgHom (R := R) J hJ x hx =
      adicEvalAlgHom J fun s => Ideal.le_radical (hx s) :=
  rfl

/-! Concrete values at the point `2` of the square-zero ideal `(2)` of
`ZMod 4`, for the geometric series `∑ Xⁿ` in one variable. -/

private abbrev twoIdeal : Ideal (ZMod 4) := Ideal.span {2}

private theorem twoIdeal_sq : twoIdeal ^ 2 = ⊥ := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
  decide

private theorem isNilpotent_twoIdeal : IsNilpotent twoIdeal :=
  ⟨2, twoIdeal_sq⟩

private theorem two_mem_twoIdeal : ∀ _ : Unit, (2 : ZMod 4) ∈ twoIdeal :=
  fun _ => Ideal.mem_span_singleton_self 2

private def geom : MvPowerSeries Unit (ZMod 4) := fun _ => 1

/-- Below degree `2` the only monomials in one variable are `1` and `X`. -/
private theorem two_le_degree (d : Unit →₀ ℕ)
    (hd : d ∉ ({0, Finsupp.single () 1} : Finset (Unit →₀ ℕ))) :
    2 ≤ d.degree := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  have e0 : d () ≠ 0 := fun h => hd.1 (Finsupp.ext fun u => by simpa using h)
  have e1 : d () ≠ 1 := fun h => hd.2 (Finsupp.ext fun u => by simpa using h)
  rw [Finsupp.degree_eq_sum, Fintype.sum_unique]
  change 2 ≤ d ()
  omega

/-- The geometric series evaluates to `1 + 2 = 3`. -/
private theorem nilpotentEval_geom :
    nilpotentEval twoIdeal isNilpotent_twoIdeal (fun _ => (2 : ZMod 4))
      two_mem_twoIdeal geom = 3 := by
  rw [nilpotentEval_eq_sum twoIdeal isNilpotent_twoIdeal twoIdeal_sq
      two_mem_twoIdeal geom _ two_le_degree,
    Finset.sum_pair (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
  simp
  decide

/-- Agreement: the adic evaluation of the geometric series is the same `3`. -/
example : adicEval twoIdeal (fun _ => (2 : ZMod 4)) geom = 3 := by
  rw [← nilpotentEval_eq_adicEval twoIdeal isNilpotent_twoIdeal
      two_mem_twoIdeal, nilpotentEval_geom]

/-- Multiplication: the square `∑ (n + 1) Xⁿ` of the geometric series
evaluates to `3 * 3 = 1`. -/
example : nilpotentEval twoIdeal isNilpotent_twoIdeal (fun _ => (2 : ZMod 4))
    two_mem_twoIdeal (geom * geom) = 1 := by
  rw [nilpotentEval_mul, nilpotentEval_geom]
  decide

/-- The same value from the coefficients of the square: `1 + 2 * 2 = 1`. -/
example : nilpotentEval twoIdeal isNilpotent_twoIdeal (fun _ => (2 : ZMod 4))
    two_mem_twoIdeal (geom * geom) = 1 := by
  rw [nilpotentEval_eq_sum twoIdeal isNilpotent_twoIdeal twoIdeal_sq
      two_mem_twoIdeal _ _ two_le_degree,
    Finset.sum_pair (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
  simp [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  decide

/-- The `AlgHom` is multiplicative on the geometric series. -/
example : nilpotentEvalAlgHom twoIdeal isNilpotent_twoIdeal
    (fun _ => (2 : ZMod 4)) two_mem_twoIdeal (geom * geom) = 1 := by
  rw [map_mul, coe_nilpotentEvalAlgHom, nilpotentEval_geom]
  decide
