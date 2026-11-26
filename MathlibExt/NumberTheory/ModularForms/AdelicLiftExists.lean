/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_isAdelicLiftOf.lean`
and
`P2M/Sol/S_CuspForm_exists_isAdelicLiftOf.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.ModularForms.AdelicLift
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Existence of adelic lifts of weight-two cusp forms

Every weight-two cusp form `g` for `Γ₀(M)`, `M ≠ 0`, has an adelic lift: a function `φ` on
`GL₂(𝔸_ℚ)` with `CuspForm.IsAdelicLiftOf g φ`. The lift is built from strong approximation
data: on `x = γ h u` with `γ ∈ GL₂(ℚ)`, `h` with trivial finite part and positive archimedean
determinant, and `u` in the finite level subgroup at `M`, it takes the value
`(g ∣[2] h_∞) i`, and it is `0` off such elements. The value does not depend on the
decomposition, because two decompositions differ by an element of `Γ₀(M)`.

## Main statements

* `CuspForm.exists_isAdelicLiftOf`: every weight-two cusp form for `Γ₀(M)`, `M ≠ 0`, has an
  adelic lift.
-/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel
  Matrix
open scoped MatrixGroups ModularForm

namespace CuspForm

namespace AdelicLiftExists

private def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal
    Rat.isReal_infinitePlace).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g') =
      LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [glArch_finEmbed, map_one, map_one]

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) =
      GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ (SpecialLinearGroup.mapGL ℚ ε)) =
      (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

private theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) =
      (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_ofClass,
    eq_ratCast]

private theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q ≤ 1 := fun v => by
    have h1 := hq v
    rw [mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
      valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one ℚ q h
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      i j = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

private theorem exists_mapGL_eq_of_integral {γ : GL (Fin 2) ℚ}
    (hγ : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈
      AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hγinv : ∀ i j, (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹ :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈
      AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), SpecialLinearGroup.mapGL ℚ δ = γ := by
  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) =
      ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]
  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ =>
        M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact RingHom.map_det (Int.castRingHom ℚ) A
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

/-- The finite place of `𝓞 ℚ` at a rational prime `p`, as Mathlib's `primesEquiv` gives it. -/
private abbrev primePlace (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp.out⟩

private theorem asIdeal_primePlace (p : ℕ) [Fact p.Prime] :
    (primePlace p).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  change Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (Ideal.span {((p : ℕ) : ℤ)}) = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem intValuation_primePlace_le_iff (p : ℕ) [Fact p.Prime] (n : ℤ) (k : ℕ) :
    (primePlace p).intValuation (n : 𝓞 ℚ) ≤ WithZero.exp (-(k : ℤ)) ↔ (p : ℤ) ^ k ∣ n := by
  rw [intValuation_le_pow_iff_dvd, asIdeal_primePlace, Ideal.span_singleton_pow,
    Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

private theorem factorization_le_count {M : ℕ} (hM : M ≠ 0) (p : ℕ) [Fact p.Prime] :
    M.factorization p ≤ (Associates.mk (primePlace p).asIdeal).count
      (Associates.mk (NumberField.AdelicLevel.ratLevel M)).factors := by
  refine (Associates.prime_pow_dvd_iff_le
    (Associates.mk_ne_zero.mpr (NumberField.AdelicLevel.ratLevel_ne_bot hM))
    (primePlace p).associates_irreducible).mp ?_
  rw [← Associates.mk_pow]
  refine Associates.mk_dvd_mk.mpr ?_
  rw [asIdeal_primePlace]
  change Ideal.span {(p : 𝓞 ℚ)} ^ _ ∣ Ideal.span {(M : 𝓞 ℚ)}
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
  exact_mod_cast map_dvd (Nat.castRingHom (𝓞 ℚ)) (Nat.ordProj_dvd M p)

private theorem pow_factorization_dvd_of_mem_idealBall {M : ℕ} (hM : M ≠ 0) (n : ℤ) (p : ℕ)
    [Fact p.Prime]
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈
      idealBall (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M)) :
    (p : ℤ) ^ M.factorization p ∣ n := by
  have hv := h (primePlace p)
  rw [FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation',
    ← map_intCast (algebraMap (𝓞 ℚ) ℚ) n,
    valuation_of_algebraMap,
    idealBound_of_ne_bot (NumberField.AdelicLevel.ratLevel_ne_bot hM)] at hv
  refine (intValuation_primePlace_le_iff p n _).mp (hv.trans ?_)
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact factorization_le_count hM p

private theorem natCast_dvd_of_mem_idealBall {M : ℕ} (hM : M ≠ 0) (n : ℤ)
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈
      idealBall (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M)) :
    (M : ℤ) ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast,
    ← Nat.factorization_prime_le_iff_dvd hM (Int.natAbs_ne_zero.mpr hn)]
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := pow_factorization_dvd_of_mem_idealBall hM n p h
  have hdvd' : p ^ M.factorization p ∣ n.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]; exact_mod_cast hdvd
  exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hn)).mp hdvd'

variable (M : ℕ)

/-- `x = γ h u` with `γ` rational, `h` with trivial finite part and positive archimedean
determinant, and `u` in the finite level subgroup at `M`. -/
private def IsLevelDecomp (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ)
    (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  u ∈ finiteLevelOne (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M) ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧
    LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
    x = globalPoints (𝓞 ℚ) ℚ γ * h * finEmbed (𝓞 ℚ) ℚ u

private def HasLevelDecomp (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsLevelDecomp M x γ h u

variable {M}

private def archVal (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

private theorem archVal_sl_mul (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (ε : SL(2, ℤ))
    (hε : ε ∈ CongruenceSubgroup.Gamma0 M) (r : GL (Fin 2) ℝ) :
    ((⇑g) ∣[(2 : ℤ)] ((ε : GL (Fin 2) ℝ) * r)) UpperHalfPlane.I =
      ((⇑g) ∣[(2 : ℤ)] r) UpperHalfPlane.I := by
  have hmem : (ε : GL (Fin 2) ℝ) ∈
      ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    ⟨ε, hε, rfl⟩
  rw [SlashAction.slash_mul, SlashInvariantForm.slash_action_eqn g _ hmem]

private theorem archVal_eq_of_isLevelDecomp (hM : M ≠ 0)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ γ' : GL (Fin 2) ℚ}
    {h h' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {u u' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : IsLevelDecomp M x γ h u) (H' : IsLevelDecomp M x γ' h' u') :
    archVal g h = archVal g h' := by
  obtain ⟨hu, hh, hpos, hx⟩ := H
  obtain ⟨hu', hh', hpos', hx'⟩ := H'
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set E := finEmbed (𝓞 ℚ) ℚ with hE
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * E u' * (E u)⁻¹ * h⁻¹ := by
    have Eq : P γ * (h * E u) = P γ' * (h' * E u') := by
      rw [← mul_assoc, ← mul_assoc, ← hx, ← hx']
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * E u') * (h * E u)⁻¹ := eq_mul_inv_of_mul_eq Eq
    rw [this, _root_.mul_inv_rev]
    group
  have hfinq : glFin (𝓞 ℚ) ℚ (P δ) = u' * u⁻¹ := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', hE, glFin_finEmbed,
      glFin_finEmbed, one_mul, inv_one, mul_one]
  have hK1 : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelOne (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M) := by
    rw [hfinq]; exact Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hu)
  have harch : LanglandsTunnell.ratArchGL2 (P δ) =
      LanglandsTunnell.ratArchGL2 h' * (LanglandsTunnell.ratArchGL2 h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv, hE,
      ratArch_finEmbed, ratArch_finEmbed, inv_one, mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((LanglandsTunnell.ratArchGL2 (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε, hε⟩ := exists_mapGL_eq_of_integral hK1.1.integral hK1.2.integral hdetpos
  have hε0 : ε ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have hll : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((ε 1 0 : ℤ) : ℚ)) ∈
        idealBall (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M) := by
      have := hK1.1.lowerLeft
      rw [← hε] at this
      rw [show (((ε 1 0 : ℤ) : ℚ)) =
            ((SpecialLinearGroup.mapGL ℚ ε : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0
          from rfl, ← glFin_globalPoints_apply]
      exact this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr (natCast_dvd_of_mem_idealBall hM _ hll)
  have hh'eq : LanglandsTunnell.ratArchGL2 h' =
      (ε : GL (Fin 2) ℝ) * LanglandsTunnell.ratArchGL2 h := by
    rw [← ratArch_globalPoints_mapGL, hε, harch, inv_mul_cancel_right]
  unfold archVal
  rw [hh'eq, archVal_sl_mul g ε hε0]

open scoped Classical in
/-- The adelic lift: `archVal g h` on `x = γ h u`, and `0` off such elements. -/
private def adelicLiftOf (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasLevelDecomp M x then archVal g H.choose_spec.choose else 0

private theorem adelicLiftOf_eq_archVal (hM : M ≠ 0)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : IsLevelDecomp M x γ h u) :
    adelicLiftOf g x = archVal g h := by
  have Hx : HasLevelDecomp M x := ⟨γ, h, u, H⟩
  unfold adelicLiftOf
  rw [dite_eq_left Hx]
  exact archVal_eq_of_isLevelDecomp hM g Hx.choose_spec.choose_spec.choose_spec H

private theorem adelicLiftOf_eq_zero (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (Hx : ¬ HasLevelDecomp M x) :
    adelicLiftOf g x = 0 := by
  unfold adelicLiftOf; rw [dite_eq_right Hx]

private theorem isLevelDecomp_globalPoints_mul_iff (γ₀ γ : GL (Fin 2) ℚ)
    (x h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    IsLevelDecomp M (globalPoints (𝓞 ℚ) ℚ γ₀ * x) γ h u ↔
      IsLevelDecomp M x (γ₀⁻¹ * γ) h u := by
  constructor
  · rintro ⟨hu, hh, hp, hx⟩
    refine ⟨hu, hh, hp, ?_⟩
    calc x = (globalPoints (𝓞 ℚ) ℚ γ₀)⁻¹ * (globalPoints (𝓞 ℚ) ℚ γ₀ * x) := by group
      _ = globalPoints (𝓞 ℚ) ℚ (γ₀⁻¹ * γ) * h * finEmbed (𝓞 ℚ) ℚ u := by
        rw [hx, map_mul, map_inv]; group
  · rintro ⟨hu, hh, hp, hx⟩
    refine ⟨hu, hh, hp, ?_⟩
    rw [hx, map_mul, map_inv]; group

private theorem isLevelDecomp_mul_finEmbed_iff {u₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ finiteLevelOne (𝓞 ℚ) ℚ (NumberField.AdelicLevel.ratLevel M)) (γ : GL (Fin 2) ℚ)
    (x h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    IsLevelDecomp M (x * finEmbed (𝓞 ℚ) ℚ u₀) γ h u ↔ IsLevelDecomp M x γ h (u * u₀⁻¹) := by
  constructor
  · rintro ⟨hu, hh, hp, hx⟩
    refine ⟨Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hu₀), hh, hp, ?_⟩
    calc x = (x * finEmbed (𝓞 ℚ) ℚ u₀) * (finEmbed (𝓞 ℚ) ℚ u₀)⁻¹ := by group
      _ = globalPoints (𝓞 ℚ) ℚ γ * h * finEmbed (𝓞 ℚ) ℚ (u * u₀⁻¹) := by
        rw [hx, map_mul, map_inv]; group
  · rintro ⟨hu, hh, hp, hx⟩
    refine ⟨?_, hh, hp, ?_⟩
    · have := Subgroup.mul_mem _ hu hu₀
      rwa [inv_mul_cancel_right] at this
    · rw [hx, map_mul, map_inv]; group

private theorem isAdelicLiftOf_adelicLiftOf (hM : M ≠ 0)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    g.IsAdelicLiftOf (adelicLiftOf g) := by
  refine ⟨fun γ₀ x => ?_, fun u₀ hu₀ x => ?_, fun h hfin hpos => ?_⟩
  · by_cases Hx : HasLevelDecomp M x
    · obtain ⟨γ, h, u, H⟩ := Hx
      have H₀ : IsLevelDecomp M (globalPoints (𝓞 ℚ) ℚ γ₀ * x) (γ₀ * γ) h u := by
        rw [isLevelDecomp_globalPoints_mul_iff, inv_mul_cancel_left]; exact H
      rw [adelicLiftOf_eq_archVal hM g H₀, adelicLiftOf_eq_archVal hM g H]
    · have Hx₀ : ¬ HasLevelDecomp M (globalPoints (𝓞 ℚ) ℚ γ₀ * x) := fun ⟨γ, h, u, H⟩ =>
        Hx ⟨γ₀⁻¹ * γ, h, u, (isLevelDecomp_globalPoints_mul_iff γ₀ γ x h u).mp H⟩
      rw [adelicLiftOf_eq_zero g Hx, adelicLiftOf_eq_zero g Hx₀]
  · by_cases Hx : HasLevelDecomp M x
    · obtain ⟨γ, h, u, H⟩ := Hx
      have H₀ : IsLevelDecomp M (x * finEmbed (𝓞 ℚ) ℚ u₀) γ h (u * u₀) := by
        rw [isLevelDecomp_mul_finEmbed_iff hu₀, mul_inv_cancel_right]; exact H
      rw [adelicLiftOf_eq_archVal hM g H₀, adelicLiftOf_eq_archVal hM g H]
    · have Hx₀ : ¬ HasLevelDecomp M (x * finEmbed (𝓞 ℚ) ℚ u₀) := fun ⟨γ, h, u, H⟩ =>
        Hx ⟨γ, h, u * u₀⁻¹, (isLevelDecomp_mul_finEmbed_iff hu₀ γ x h u).mp H⟩
      rw [adelicLiftOf_eq_zero g Hx, adelicLiftOf_eq_zero g Hx₀]
  · have H : IsLevelDecomp M h 1 h 1 :=
      ⟨Subgroup.one_mem _, hfin, hpos, by rw [map_one, map_one, one_mul, mul_one]⟩
    rw [adelicLiftOf_eq_archVal hM g H]
    rfl

end AdelicLiftExists

/-- Every weight-two cusp form for `Γ₀(M)` with `M ≠ 0` has an adelic lift. -/
public theorem exists_isAdelicLiftOf {M : ℕ} (hM : M ≠ 0)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ φ : NumberField.AdelicGL2 (𝓞 ℚ) ℚ → ℂ, g.IsAdelicLiftOf φ :=
  ⟨AdelicLiftExists.adelicLiftOf g, AdelicLiftExists.isAdelicLiftOf_adelicLiftOf hM g⟩

end CuspForm

end
