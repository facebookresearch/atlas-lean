/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOverOfTranscendental
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.Kaehler.Basic
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors
import MathlibExt.RingTheory.Kaehler.Transcendental

/-! # Tests for curve function fields obtained from a transcendental element -/

@[expose] public section

namespace AlgebraicCurve

-- `exactSource` consumer with the original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.IsCurveOver K F :=
  isCurveOver_of_transcendental_of_perfectField htr hfd

-- The separable variant, with its original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F :=
  isCurveOver_of_transcendental htr hfd hsep

-- A finite separable extension of `RatFunc K` has principal divisors of degree zero.
example {K : Type*} [Field K] (E : Type*) [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E :=
  hasPrincipalDivisors_of_finiteDimensional_of_isSeparable K E

-- Boundary: transcendence matters. `K` is finite over `K⟮1⟯`, but its Kähler differentials over
-- `K` vanish, so `K` is not the function field of a curve over `K`.
example (K : Type*) [Field K] : ¬ IsCurveOver K K := by
  intro h
  have h1 := h.kaehler_free_rank_one.2
  have : Subsingleton Ω[K⁄K] :=
    KaehlerDifferential.subsingleton_of_surjective K K Function.surjective_id
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

-- Positive instance: the hypotheses hold for `x = X` in `RatFunc K`, since `K⟮X⟯ = ⊤`.
example (K : Type*) [Field K] : IsCurveOver K (RatFunc K) := by
  have htop : IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)) = ⊤ := RatFunc.adjoin_X
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Algebra.IsSeparable.of_equiv_equiv IntermediateField.topEquiv.symm.toRingEquiv
      (RingEquiv.refl (RatFunc K)) (RingHom.ext fun _ => rfl)
  exact isCurveOver_of_transcendental RatFunc.transcendental_X hfd hsep

-- Positive instance of the perfect-field version: no separability hypothesis is needed.
example (K : Type*) [Field K] [PerfectField K] : IsCurveOver K (RatFunc K) := by
  have htop : IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)) = ⊤ := RatFunc.adjoin_X
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  exact isCurveOver_of_transcendental_of_perfectField RatFunc.transcendental_X hfd

-- The instance makes the `IsCurveOver` API available for `RatFunc K`.
example (K : Type*) [Field K] : IsCurveOver K (RatFunc K) := inferInstance

example (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) := inferInstance

example (K : Type*) [Field K] (v : Place K (RatFunc K)) : Module.Finite K v.ResidueField :=
  inferInstance

-- A perfect base field and a generator that is not separating: over a perfect field of
-- characteristic `p`, take `x = X ^ p` in `RatFunc K`. Then `RatFunc K` is finite over `K⟮x⟯`,
-- and the perfect-field version applies.
example (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [PerfectField K] [CharP K p] :
    IsCurveOver K (RatFunc K) := by
  set E := IntermediateField.adjoin K ({RatFunc.X ^ p} : Set (RatFunc K))
  have hint : IsIntegral E (RatFunc.X : RatFunc K) := by
    refine ⟨Polynomial.X ^ p - Polynomial.C
      ⟨RatFunc.X ^ p, IntermediateField.mem_adjoin_simple_self K _⟩,
      Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
    simp
  have hfd : FiniteDimensional E (RatFunc K) := by
    have := IntermediateField.adjoin.finiteDimensional hint
    rw [RatFunc.IntermediateField.adjoin_X E] at this
    exact (IntermediateField.topEquiv (F := E) (E := RatFunc K)).toLinearEquiv.finiteDimensional
  exact isCurveOver_of_transcendental_of_perfectField
    (RatFunc.transcendental_X.pow hp.out.pos) hfd

-- ... while `RatFunc K` is not separable over `K⟮X ^ p⟯`, so `isCurveOver_of_transcendental` does
-- not apply to this generator: `D (X ^ p) = p • X ^ (p - 1) • D X = 0` would span the Kähler
-- differentials, but `D X ≠ 0`.
example (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ¬ Algebra.IsSeparable (IntermediateField.adjoin K ({RatFunc.X ^ p} : Set (RatFunc K)))
      (RatFunc K) := by
  intro hsep
  have htop := KaehlerDifferential.span_D_eq_top_of_transcendental K (RatFunc.X ^ p)
    (RatFunc.transcendental_X.pow hp.out.pos)
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (RatFunc K), CharP.cast_eq_zero,
    zero_smul, Set.singleton_zero, Submodule.span_zero] at htop
  have hsepX : Algebra.IsSeparable (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [RatFunc.adjoin_X]
    exact Algebra.IsSeparable.of_equiv_equiv IntermediateField.topEquiv.symm.toRingEquiv
      (RingEquiv.refl (RatFunc K)) (RingHom.ext fun _ => rfl)
  refine KaehlerDifferential.D_ne_zero_of_transcendental K (RatFunc.X : RatFunc K)
    RatFunc.transcendental_X ?_
  have hmem : KaehlerDifferential.D K (RatFunc K) RatFunc.X ∈
      (⊤ : Submodule (RatFunc K) Ω[RatFunc K⁄K]) := Submodule.mem_top
  rw [← htop] at hmem
  exact (Submodule.mem_bot (RatFunc K)).mp hmem

-- The `RatFunc K`-algebra structure from a separating transcendental element, used the way
-- `isCurveOver_of_transcendental` and the genus theorem use it.
example {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasPrincipalDivisors K F := by
  obtain ⟨_, _, _, _, -, -⟩ := exists_ratFunc_algebra_of_transcendental htr hfd hsep
  exact hasPrincipalDivisors_of_finiteDimensional_of_isSeparable K F

-- The structure is the one of `X ↦ x`: it sends `X` to `x`, hence every polynomial expression in
-- `X` to the same expression in `x`, and `F` has the same degree over it as over `K⟮x⟯`.
example {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ _ : Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F ∧
      algebraMap (RatFunc K) F (RatFunc.X ^ 2 + 1) = x ^ 2 + 1 ∧
      Module.finrank (RatFunc K) F =
        Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  obtain ⟨_, hT, -, -, hX, hdeg⟩ := exists_ratFunc_algebra_of_transcendental htr hfd hsep
  exact ⟨_, hT, by rw [map_add, map_pow, map_one, hX], hdeg.symm⟩

-- Consumer of `Place.finite_residueField_restrict`: in any finite extension `E` of `RatFunc K`,
-- separable or not, every residue field is finite over `K`.
example {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra (RatFunc K) E]
    [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E] (w : Place K E) :
    Module.Finite K w.ResidueField := by
  have := RationalFunctionField.finite_residueField (w.restrict (RatFunc K))
  have := Place.finite_residueField_restrict (F := RatFunc K) w
  exact Module.Finite.trans (w.restrict (RatFunc K)).ResidueField w.ResidueField

-- Universe check: the base field and the function field may live in different universes.
universe u v in
example {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F :=
  isCurveOver_of_transcendental_of_perfectField htr hfd

end AlgebraicCurve
