/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/NumberTheory/Height/Northcott.lean,
TauCeti/NumberTheory/Height/Basic.lean,
TauCeti/LinearAlgebra/Projectivization/Basic.lean.
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Authors: Ralf Stephan; Ralf Stephan and Zayn Blore in the normalization file.
Released under Apache 2.0, as in those source headers.

Those proofs credit rwst/Subspace-Theorems, revision
e443c2479e19f7665b31d8e94e2317c8ced1ca06,
ArithmeticHeights/Northcott.lean, also under Apache 2.0.
Modifications: consolidate the required lemmas in one standalone module,
adapt the representative API, and expose the number-field specialization.
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Order.Northcott

/-!
# Northcott finiteness for actual projective-point heights

The points are Mathlib projectivizations, and the height is the actual
product of absolute-value factors of a representative. Normalization at a
nonzero coordinate bounds every affine ratio by that height; scalar
Northcott then gives a finite product containing all such representatives.

The general projective result already exists in TauCeti. This is a completed
source port into the pinned Mathlib setting, with no duplicate Wanted goal.
It does not define an arbitrary height or claim general Faltings/Arakelov
theory.

References: Hindry–Silverman, *Diophantine Geometry*, Theorem B.2.3;
Bombieri–Gubler, *Heights in Diophantine Geometry*, Theorem 2.4.9.
-/

@[expose] public noncomputable section

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]
  {ι : Type*} [Finite ι]

/-- Scalar height of a coordinate ratio is bounded by tuple height. -/
lemma mulHeight₁_div_le_mulHeight (x : ι → K) (i j : ι) :
    mulHeight₁ (x i / x j) ≤ mulHeight x := by
  rw [mulHeight₁_div_eq_mulHeight]
  simpa only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq] using
    mulHeight_comp_le ![i, j] x

end Height

namespace Projectivization

variable {K : Type*} [Field K] {ι : Type*}

/-- A projective point can be normalized at any nonzero coordinate. -/
lemma exists_rep_apply_eq_one_of_ne_zero (x : Projectivization K (ι → K))
    {i : ι} (hi : x.rep i ≠ 0) :
    ∃ (v : ι → K) (hv : v ≠ 0),
      v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧ mk K v hv = x := by
  refine ⟨(x.rep i)⁻¹ • x.rep,
    smul_ne_zero (inv_ne_zero hi) x.rep_nonzero,
    inv_mul_cancel₀ hi, fun j => (div_eq_inv_mul _ _).symm, ?_⟩
  conv_rhs => rw [← x.mk_rep]
  exact (mk_eq_mk_iff' K _ _ _ x.rep_nonzero).mpr ⟨_, rfl⟩

/-- Every actual projective point has a normalized affine representative. -/
lemma exists_rep_apply_eq_one (x : Projectivization K (ι → K)) :
    ∃ (v : ι → K) (hv : v ≠ 0) (i : ι),
      v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧ mk K v hv = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  obtain ⟨v, hv, h1, hratio, hmk⟩ := exists_rep_apply_eq_one_of_ne_zero x hi
  exact ⟨v, hv, i, h1, hratio, hmk⟩

open Height

variable [AdmissibleAbsValues K] [Finite ι]

/-- Projective multiplicative height inherits scalar Northcott finiteness. -/
instance instNorthcottMulHeight [Northcott (mulHeight₁ (K := K))] :
    Northcott (mulHeight (K := K) (ι := ι)) where
  finite_le B := by
    have hpi : {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B}.Finite :=
      Set.Finite.pi' fun _ : ι =>
        Northcott.finite_le (h := mulHeight₁ (K := K)) B
    have hsub :
        (Subtype.val ⁻¹' {v : ι → K | ∀ i, mulHeight₁ (v i) ≤ B} :
          Set {w : ι → K // w ≠ 0}).Finite :=
      hpi.preimage Subtype.val_injective.injOn
    refine (hsub.image (mk' K)).subset ?_
    rintro x hx
    obtain ⟨v, hv, i₀, hi₀, _, rfl⟩ := exists_rep_apply_eq_one x
    refine ⟨⟨v, hv⟩, fun i => ?_, rfl⟩
    have h := Height.mulHeight₁_div_le_mulHeight v i i₀
    rw [hi₀, div_one] at h
    exact h.trans (by rwa [← mulHeight_mk hv])

/-- Projective logarithmic height inherits multiplicative finiteness. -/
instance instNorthcottLogHeight
    [Northcott (mulHeight (K := K) (ι := ι))] :
    Northcott (logHeight (K := K) (ι := ι)) := by
  have heq : logHeight (K := K) (ι := ι) = Real.log ∘ mulHeight :=
    funext logHeight_eq_log_mulHeight
  rw [heq]
  exact Northcott.comp_of_bddAbove _ _ fun B =>
    bddAbove_def.mpr ⟨Real.exp B, fun _ => Real.le_exp_of_log_le⟩

end Projectivization

namespace MathlibExt.NumberTheory.ProjectiveNorthcott

/-- Bounded actual projective height over a fixed number field gives finitely
many points in every finite projective dimension. -/
theorem finite_projective_logHeight_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (B : ℝ) :
    {x : Projectivization K (Fin (n + 1) → K) |
      Projectivization.logHeight x ≤ B}.Finite :=
  Northcott.finite_le B

end MathlibExt.NumberTheory.ProjectiveNorthcott
