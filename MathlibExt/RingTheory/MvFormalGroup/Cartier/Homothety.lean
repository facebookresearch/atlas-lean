/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_MvFormalGroup_CartierModuleHomothety.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Operators

/-!
# Homotheties on Cartier modules

For `a : R`, `CartierModule.homothety a` precomposes with the Teichmüller family
`WittLaw.teichFam a`, i.e. the substitution `X n ↦ a ^ p ^ n • X n`. It is multiplicative in
`a` (`homothety_mul`), satisfies `F ∘ [a] = [a ^ p] ∘ F` (`frobenius_homothety`) and, in
characteristic `p`, `[a] ∘ V = V ∘ [a ^ p]` (`homothety_verschiebung`), and commutes with the
action of formal group homomorphisms (`map_homothety`).

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def teichFam (a : R) : ℕ → MvPowerSeries ℕ R := fun n => (a ^ p ^ n) • X n

variable {p}

omit hp in
@[simp] theorem teichFam_apply (a : R) (n : ℕ) : teichFam p a n = (a ^ p ^ n) • X n := rfl

omit hp in
theorem teichFam_eq_smul_X (a : R) :
    teichFam p a = (fun n => a ^ p ^ n) • (X : ℕ → MvPowerSeries ℕ R) := rfl

omit hp in
theorem constantCoeff_teichFam (a : R) (n : ℕ) : (teichFam p a n).constantCoeff = 0 := by
  rw [teichFam_apply, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

omit hp in
theorem hasSubst_teichFam (a : R) : HasSubst (teichFam p a) := HasSubst.smul_X _

omit hp in
theorem subst_teichFam (a : R) (f : MvPowerSeries ℕ R) :
    subst (teichFam p a) f = rescale (fun n => a ^ p ^ n) f :=
  (rescale_eq_subst _ f).symm

omit hp in
theorem pairFam_teichFam (a : R) :
    pairFam (teichFam p a) = (fun im : Fin 2 × ℕ => a ^ p ^ im.2) • X := by
  funext ⟨i, m⟩
  rw [pairFam_apply, teichFam_apply, subst_smul (hasSubst_blk i), subst_X (hasSubst_blk i)]
  rfl

theorem isEndo_teichFam (a : R) : IsEndo p (teichFam p a) := by
  refine ⟨hasSubst_teichFam a, constantCoeff_teichFam a, fun n => ?_⟩
  rw [teichFam_apply, subst_smul (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    pairFam_teichFam, ← rescale_eq_subst]
  ext e
  rw [coeff_smul, coeff_rescale]
  by_cases he : coeff e (addFam p R n) = 0
  · rw [he, mul_zero, mul_zero]
  · congr 1
    rw [← weight_eq_of_coeff_addFam_ne_zero p R he, Finsupp.weight_apply, Finsupp.prod,
      Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun im _ => ?_
    rw [← pow_mul, weight_apply, one_mul, smul_eq_mul, mul_comm]

omit hp in
theorem teichFam_one : teichFam p (1 : R) = X := by
  funext n
  rw [teichFam_apply, one_pow, one_smul]

theorem teichFam_zero : teichFam p (0 : R) = 0 := by
  funext n
  rw [teichFam_apply, zero_pow (pow_ne_zero n hp.out.ne_zero), zero_smul, Pi.zero_apply]

omit hp in
theorem subst_teichFam_teichFam (a b : R) (n : ℕ) :
    subst (teichFam p a) (teichFam p b n) = teichFam p (a * b) n := by
  rw [teichFam_apply, subst_smul (hasSubst_teichFam a), subst_X (hasSubst_teichFam a),
    teichFam_apply, teichFam_apply, smul_smul, mul_pow, mul_comm]

theorem subst_teichFam_frobFam (a : R) (n : ℕ) :
    subst (teichFam p a) (frobFam p R n) = subst (frobFam p R) (teichFam p (a ^ p) n) := by
  rw [frobFam_apply, subst_pow (hasSubst_teichFam _), subst_X (hasSubst_teichFam _), teichFam_apply,
    smul_pow, teichFam_apply, subst_smul hasSubst_frobFam, subst_X hasSubst_frobFam, frobFam_apply,
    ← pow_mul, ← pow_mul, mul_comm (p ^ n) p]

omit hp in
theorem subst_teichFam_verFam (a : R) (n : ℕ) :
    subst (teichFam p (a ^ p)) (verFam R n) = subst (verFam R) (teichFam p a n) := by
  rw [teichFam_apply, subst_smul hasSubst_verFam, subst_X hasSubst_verFam]
  cases n with
  | zero =>
    rw [verFam_zero, ← coe_substAlgHom (hasSubst_teichFam _), map_zero, smul_zero]
  | succ n =>
    rw [verFam_succ, subst_X (hasSubst_teichFam _), teichFam_apply, ← pow_mul, ← pow_succ']

omit hp in
theorem subst_curveFam_teichFam (a : R) (n : ℕ) :
    subst (CartierModule.curveFam R) (teichFam p a n) =
      PowerSeries.rescale a (CartierModule.curveFam R n) := by
  rw [teichFam_apply, subst_smul CartierModule.hasSubst_curveFam,
    subst_X CartierModule.hasSubst_curveFam]
  cases n with
  | zero =>
    change (a ^ p ^ 0) • (PowerSeries.X : PowerSeries R) = PowerSeries.rescale a PowerSeries.X
    rw [pow_zero, pow_one, PowerSeries.rescale_X, PowerSeries.smul_eq_C_mul]
  | succ n =>
    change (a ^ p ^ (n + 1)) • (0 : PowerSeries R) = PowerSeries.rescale a 0
    rw [smul_zero, map_zero]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

/-- **Homothety of a Cartier module.** For a commutative formal group law `Φ` over a commutative
ring `R` and `a : R`, the homothety `[a]` precomposes each point of the Cartier module with
multiplication by the Teichmüller representative of `a`, the substitution
`X n ↦ a ^ p ^ n • X n`. -/
def homothety [Φ.IsComm] (a : R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_teichFam a)

theorem homothety_eq_precomp [Φ.IsComm] (a : R) :
    (homothety a : CartierModule p Φ →+ CartierModule p Φ) = precomp (WittLaw.isEndo_teichFam a) :=
  rfl

@[simp] theorem toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    (homothety a f).toPowerSeries = fun j => subst (WittLaw.teichFam p a) (f.toPowerSeries j) := rfl

theorem toPowerSeries_homothety_eq_rescale [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    (homothety a f).toPowerSeries j = rescale (fun n => a ^ p ^ n) (f.toPowerSeries j) :=
  WittLaw.subst_teichFam a _

theorem coeff_toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d)
    (e : ℕ →₀ ℕ) :
    coeff e ((homothety a f).toPowerSeries j) =
      (e.prod fun n k => (a ^ p ^ n) ^ k) * coeff e (f.toPowerSeries j) := by
  rw [toPowerSeries_homothety_eq_rescale, coeff_rescale]

theorem homothety_one [Φ.IsComm] (f : CartierModule p Φ) : homothety (1 : R) f = f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_one]
  exact congrFun subst_self _

theorem homothety_zero_left [Φ.IsComm] (f : CartierModule p Φ) : homothety (0 : R) f = 0 := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_zero]
  exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)

theorem homothety_mul [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety (a * b) f = homothety a (homothety b f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ f).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, toPowerSeries_precomp]
  change subst (WittLaw.teichFam p (a * b)) (f.toPowerSeries j) = _
  congr 1
  funext n
  rw [WittLaw.subst_teichFam_teichFam]

theorem homothety_comm [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety a (homothety b f) = homothety b (homothety a f) := by
  rw [← homothety_mul, mul_comm, homothety_mul]

theorem homothety_verschiebung [Φ.IsComm] [CharP R p] (a : R) (f : CartierModule p Φ) :
    homothety a (verschiebung f) = verschiebung (homothety (a ^ p) f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_teichFam_frobFam a n

theorem frobenius_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    frobenius (homothety a f) = homothety (a ^ p) (frobenius f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact (WittLaw.subst_teichFam_verFam a n).symm

theorem homothety_nsmul [Φ.IsComm] (a : R) (n : ℕ) (f : CartierModule p Φ) :
    homothety a (n • f) = n • homothety a f :=
  map_nsmul _ _ _

theorem map_homothety [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (a : R) (f : CartierModule p Φ) :
    map φ (homothety a f) = homothety a (map φ f) :=
  map_precomp φ _ f

theorem endAct_homothety [Φ.IsComm] (φ : MvFormalGroup.End Φ) (a : R) (f : CartierModule p Φ) :
    endAct φ (homothety a f) = homothety a (endAct φ f) :=
  map_precomp φ _ f

theorem tangent_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    tangent (homothety a f) = a • tangent f := by
  funext j
  rw [tangent_apply, coeff_toPowerSeries_homothety, Pi.smul_apply, tangent_apply, smul_eq_mul,
    Finsupp.prod_single_index (by simp), pow_zero, pow_one, pow_one]

theorem curve_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    curve (homothety a f) j = PowerSeries.rescale a (curve f j) := by
  rw [curve_apply, toPowerSeries_homothety, curve_apply,
    subst_comp_subst_apply (WittLaw.hasSubst_teichFam a) hasSubst_curveFam,
    PowerSeries.rescale_eq, rescale_eq_subst,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.smul_X _)]
  congr 1
  funext n
  rw [WittLaw.subst_curveFam_teichFam, PowerSeries.rescale_eq, rescale_eq_subst]

namespace Examples

theorem homothety_addLinear (a : R) (v : Fin d → R) :
    homothety a (addLinear p v) = addLinear p (a • v) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_homothety, toPowerSeries_addLinear]
  change subst (WittLaw.teichFam p a) ((addLinear p v).toPowerSeries i) = _
  rw [toPowerSeries_addLinear, subst_smul (WittLaw.hasSubst_teichFam a),
    subst_X (WittLaw.hasSubst_teichFam a), WittLaw.teichFam_apply, pow_zero, pow_one, smul_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

end Examples

end CartierModule

end MvFormalGroup

end
