/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files under `Definitions/`,
`Theorems/` and `P2M/Sol/`:

`Def_MvPolynomial_CrossingQuotient.lean`,
`Def_MvPolynomial_CrossingResolution.lean`,
`Def_MvPolynomial_CrossingResolutionScheme.lean`,
`Thm_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing.lean`,
`S_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing.lean`,
`S_MvPolynomial_CrossingQuotient_Resolution_isSeparated.lean`,
`S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing.lean`,
`S_MvPolynomial_CrossingQuotient_Resolution_valuativeCriterion_existence_toCrossing.lean`
and `S_MvPolynomial_CrossingQuotient_exists_comp_resolutionChart_eq_of_valuationRing.lean`
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
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib APIs directly.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import MathlibExt.RingTheory.MvPolynomial.CrossingQuotient

/-!
# Properness of the crossing resolution morphism

The resolution of the crossing `X * Y = t ^ e` over a commutative ring `W` is glued from `e`
affine charts, each a copy of the crossing `X * Y = t`. Its morphism to the crossing scheme of
`t ^ e` is proper: it is separated, locally of finite type, quasi-compact, and satisfies the
existence part of the valuative criterion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type u} [CommRing W] (t : W)

/-- The localization of the crossing quotient at `Y`, the overlap of adjacent charts. -/
abbrev OverlapRing : Type u := Localization.Away (V t)

/-- The localization of the crossing quotient at `X * Y`, the common torus of all charts. -/
abbrev TorusRing : Type u :=
  Localization.Away (algebraMap (CrossingQuotient W t) (OverlapRing t) (U t))

instance isLocalization_away_torusRing :
    IsLocalization.Away (algebraMap W (CrossingQuotient W t) t) (TorusRing t) := by
  rw [← U_mul_V]; infer_instance

abbrev xT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (U t)

abbrev yT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (V t)

abbrev tT : TorusRing t := algebraMap W (TorusRing t) t

abbrev tinv : TorusRing t :=
  IsLocalization.Away.invSelf (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)

theorem xT_mul_yT : xT t * yT t = tT t := by
  rw [← map_mul, U_mul_V, ← IsScalarTower.algebraMap_apply]

theorem tT_mul_tinv : tT t * tinv t = 1 := by
  change algebraMap W (TorusRing t) t * _ = 1
  rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t) t]
  exact IsLocalization.Away.mul_invSelf _

theorem tinv_mul_tT : tinv t * tT t = 1 := by rw [mul_comm, tT_mul_tinv]

theorem isUnit_tT : IsUnit (tT t) := IsUnit.of_mul_eq_one _ (tT_mul_tinv t)

theorem tinv_pow_mul_tT_pow (i : ℕ) : tinv t ^ i * tT t ^ i = 1 := by
  rw [← mul_pow, tinv_mul_tT, one_pow]

theorem tT_pow_mul_tinv_pow (i : ℕ) : tT t ^ i * tinv t ^ i = 1 := by
  rw [← mul_pow, tT_mul_tinv, one_pow]

def twist₀ (a b : TorusRing t) (hab : a * b = 1) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  lift t (xT t * a) (yT t * b) (by rw [mul_mul_mul_comm, xT_mul_yT, hab, mul_one])

theorem twist₀_U (a b : TorusRing t) (hab : a * b = 1) : twist₀ t a b hab (U t) = xT t * a :=
  lift_U _ _ _ _

theorem twist₀_V (a b : TorusRing t) (hab : a * b = 1) : twist₀ t a b hab (V t) = yT t * b :=
  lift_V _ _ _ _

theorem isUnit_twist₀_apply (a b : TorusRing t) (hab : a * b = 1) :
    IsUnit ((twist₀ t a b hab).toRingHom (algebraMap W (CrossingQuotient W t) t)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact isUnit_tT t

def twistRingHom (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →+* TorusRing t :=
  IsLocalization.Away.lift (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)
    (g := (twist₀ t a b hab).toRingHom) (isUnit_twist₀_apply t a b hab)

theorem twistRingHom_algebraMap (a b : TorusRing t) (hab : a * b = 1) (c : CrossingQuotient W t) :
    twistRingHom t a b hab (algebraMap _ _ c) = twist₀ t a b hab c :=
  IsLocalization.Away.lift_eq (S := TorusRing t) _ (isUnit_twist₀_apply t a b hab) c

/-- The `W`-algebra endomorphism of the torus ring rescaling `X` by `a` and `Y` by `b`. -/
def twist (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →ₐ[W] TorusRing t :=
  { twistRingHom t a b hab with
    commutes' := fun w => by
      change twistRingHom t a b hab (algebraMap W (TorusRing t) w) = _
      rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t) w,
        twistRingHom_algebraMap]
      exact (twist₀ t a b hab).commutes w }

variable {t}

theorem twist_algebraMap (a b : TorusRing t) (hab : a * b = 1) (c : CrossingQuotient W t) :
    twist t a b hab (algebraMap _ _ c) = twist₀ t a b hab c :=
  twistRingHom_algebraMap t a b hab c

theorem twist_xT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (xT t) = xT t * a := by
  rw [twist_algebraMap, twist₀_U]

theorem twist_yT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (yT t) = yT t * b := by
  rw [twist_algebraMap, twist₀_V]

theorem twist_tT (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (tT t) = tT t :=
  AlgHom.commutes _ _

theorem twist_tinv (a b : TorusRing t) (hab : a * b = 1) : twist t a b hab (tinv t) = tinv t := by
  have h1 : twist t a b hab (tinv t) * tT t = 1 := by
    rw [← twist_tT a b hab, ← map_mul, tinv_mul_tT, map_one]
  calc twist t a b hab (tinv t) = twist t a b hab (tinv t) * (tT t * tinv t) := by
        rw [tT_mul_tinv, mul_one]
    _ = tinv t := by rw [← mul_assoc, h1, one_mul]

theorem twist_comp_algebraMap (a b : TorusRing t) (hab : a * b = 1) :
    (twist t a b hab).comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) =
      twist₀ t a b hab :=
  AlgHom.ext fun c => twist_algebraMap a b hab c

theorem algHom_ext_torus {A : Type*} [CommRing A] [Algebra W A] {f g : TorusRing t →ₐ[W] A}
    (hx : f (xT t) = g (xT t)) (hy : f (yT t) = g (yT t)) : f = g := by
  have key : f.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) =
      g.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · exact hx
    · exact hy
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap W (CrossingQuotient W t) t))
    (S := TorusRing t)
  exact RingHom.ext fun c => congrArg (fun φ : CrossingQuotient W t →ₐ[W] A => φ c) key

theorem twist_comp_twist (a b : TorusRing t) (hab : a * b = 1)
    (ha : twist t a b hab a = a) (hb : twist t a b hab b = b) :
    (twist t a b hab).comp (twist t b a ((mul_comm b a).trans hab)) =
        AlgHom.id W (TorusRing t) := by
  apply algHom_ext_torus
  · rw [AlgHom.comp_apply, twist_xT, map_mul, twist_xT, hb, mul_assoc, hab, mul_one,
      AlgHom.id_apply]
  · rw [AlgHom.comp_apply, twist_yT, map_mul, twist_yT, ha, mul_assoc, mul_comm b a, hab, mul_one,
      AlgHom.id_apply]

theorem twist_tinv_pow (a b : TorusRing t) (hab : a * b = 1) (i : ℕ) :
    twist t a b hab (tinv t ^ i) = tinv t ^ i := by rw [map_pow, twist_tinv]

theorem twist_tT_pow (a b : TorusRing t) (hab : a * b = 1) (i : ℕ) :
    twist t a b hab (tT t ^ i) = tT t ^ i := by rw [map_pow, twist_tT]

variable (t)

/-- The automorphism of the torus ring rescaling `X` by `t⁻¹ ^ i` and `Y` by `t ^ i`. -/
def twistEquiv (i : ℕ) : TorusRing t ≃ₐ[W] TorusRing t :=
  AlgEquiv.ofAlgHom (twist t (tinv t ^ i) (tT t ^ i) (tinv_pow_mul_tT_pow t i))
    (twist t (tT t ^ i) (tinv t ^ i) (tT_pow_mul_tinv_pow t i))
    (twist_comp_twist _ _ _ (twist_tinv_pow _ _ _ i) (twist_tT_pow _ _ _ i))
    (twist_comp_twist _ _ _ (twist_tT_pow _ _ _ i) (twist_tinv_pow _ _ _ i))

theorem twistEquiv_xT (i : ℕ) : twistEquiv t i (xT t) = xT t * tinv t ^ i := twist_xT _ _ _

theorem twistEquiv_yT (i : ℕ) : twistEquiv t i (yT t) = yT t * tT t ^ i := twist_yT _ _ _

/-- The inclusion of the `i`-th chart ring into the torus ring. -/
def torusChart (i : ℕ) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t))

/-- The inclusion of the `i`-th overlap ring into the torus ring. -/
def torusOverlap (i : ℕ) : OverlapRing t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (OverlapRing t) (TorusRing t))

theorem torusChart_U (i : ℕ) : torusChart t i (U t) = xT t * tinv t ^ i := twistEquiv_xT t i

theorem torusChart_V (i : ℕ) : torusChart t i (V t) = yT t * tT t ^ i := twistEquiv_yT t i

theorem torusOverlap_algebraMap (i : ℕ) (c : CrossingQuotient W t) :
    torusOverlap t i (algebraMap _ _ c) = torusChart t i c := by
  change twistEquiv t i (algebraMap (OverlapRing t) (TorusRing t) (algebraMap _ _ c)) =
    twistEquiv t i (algebraMap _ _ c)
  rw [← IsScalarTower.algebraMap_apply]

theorem torusOverlap_comp_toAlgHom (i : ℕ) :
    (torusOverlap t i).comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (OverlapRing t)) =
      torusChart t i :=
  AlgHom.ext (torusOverlap_algebraMap t i)

theorem algHom_ext_chart {s : W} {A : Type*} [CommRing A] [Algebra W A]
    {f g : CrossingQuotient W s →ₐ[W] A}
    (hx : f (U s) = g (U s)) (hy : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  · exact hx
  · exact hy

theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type*} [CommRing A] {a b c : A}
    (hb : a * b = 1) (hc : c * a = 1) : b = c := by
  calc b = (c * a) * b := by rw [hc, one_mul]
    _ = c * (a * b) := by ring
    _ = c := by rw [hb, mul_one]

theorem torusOverlap_comp_transitionUp (i : ℕ) :
    (torusOverlap t i).comp (transitionUp t) = torusChart t (i + 1) := by
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, transitionUp_U, torusChart_U]
    have h1 : torusOverlap t i (algebraMap _ _ (V t)) *
        torusOverlap t i (IsLocalization.Away.invSelf (V t)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    rw [torusOverlap_algebraMap, torusChart_V] at h1
    apply eq_of_mul_eq_one_of_mul_eq_one h1
    have h2 := xT_mul_yT t
    have h3 := tinv_mul_tT t
    have h4 := tinv_pow_mul_tT_pow t i
    linear_combination (tinv t ^ (i + 1) * tT t ^ i) * h2 + (tinv t * tT t) * h4 + h3
  · rw [AlgHom.comp_apply, transitionUp_V, map_mul, AlgHom.commutes, torusOverlap_algebraMap,
      torusChart_V, torusChart_V, pow_succ]
    change tT t * (yT t * tT t ^ i) = yT t * (tT t ^ i * tT t)
    ring

section transition

def transitionUpAway : Localization.Away (U t) →+* OverlapRing t :=
  IsLocalization.Away.lift (S := Localization.Away (U t)) (U t) (g := (transitionUp t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V t)))

def transitionDownAway : OverlapRing t →+* Localization.Away (U t) :=
  IsLocalization.Away.lift (S := OverlapRing t) (V t) (g := (transitionDown t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionDown_V]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U t)))

theorem transitionUpAway_algebraMap (c : CrossingQuotient W t) :
    transitionUpAway t (algebraMap _ _ c) = transitionUp t c :=
  IsLocalization.Away.lift_eq (S := Localization.Away (U t)) (U t) _ c

theorem transitionDownAway_algebraMap (c : CrossingQuotient W t) :
    transitionDownAway t (algebraMap _ _ c) = transitionDown t c :=
  IsLocalization.Away.lift_eq (S := OverlapRing t) (V t) _ c

theorem transitionUpAway_comp_algebraMap :
    (transitionUpAway t).comp (algebraMap (CrossingQuotient W t) (Localization.Away (U t))) =
      (transitionUp t).toRingHom :=
  IsLocalization.Away.lift_comp (S := Localization.Away (U t)) (U t) _

theorem mk_C_eq_algebraMap (s w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

theorem transitionDownAway_comp_transitionUpAway :
    (transitionDownAway t).comp (transitionUpAway t) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (U t))
  rw [RingHom.comp_assoc, transitionUpAway_comp_algebraMap, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change transitionDownAway t (transitionUp t (mk t (C w))) = algebraMap _ _ (mk t (C w))
    rw [mk_C_eq_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
      (OverlapRing t), transitionDownAway_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro j
    fin_cases j
    · change transitionDownAway t (transitionUp t (U t)) = algebraMap _ _ (U t)
      rw [transitionUp_U]
      have h1 : transitionDownAway t (algebraMap _ _ (V t)) *
          transitionDownAway t (IsLocalization.Away.invSelf (V t)) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      rw [transitionDownAway_algebraMap, transitionDown_V] at h1
      exact eq_of_mul_eq_one_of_mul_eq_one h1 (IsLocalization.Away.mul_invSelf (U t))
    · change transitionDownAway t (transitionUp t (V t)) = algebraMap _ _ (V t)
      rw [transitionUp_V, map_mul, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (OverlapRing t), transitionDownAway_algebraMap, transitionDownAway_algebraMap,
        AlgHom.commutes, transitionDown_V, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (Localization.Away (U t)), ← U_mul_V, map_mul, mul_comm (algebraMap _ _ (U t)), mul_assoc,
        IsLocalization.Away.mul_invSelf, mul_one]

theorem transitionUpAway_comp_transitionDownAway :
    (transitionUpAway t).comp (transitionDownAway t) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (V t))
  rw [RingHom.comp_assoc, transitionDownAway, IsLocalization.Away.lift_comp, RingHom.id_comp]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change transitionUpAway t (transitionDown t (mk t (C w))) = algebraMap _ _ (mk t (C w))
    rw [mk_C_eq_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
      (Localization.Away (U t)), transitionUpAway_algebraMap, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro j
    fin_cases j
    · change transitionUpAway t (transitionDown t (U t)) = algebraMap _ _ (U t)
      rw [transitionDown_U, map_mul, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (Localization.Away (U t)), transitionUpAway_algebraMap, transitionUpAway_algebraMap,
        AlgHom.commutes, transitionUp_U, IsScalarTower.algebraMap_apply W (CrossingQuotient W t)
        (OverlapRing t), ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    · change transitionUpAway t (transitionDown t (V t)) = algebraMap _ _ (V t)
      rw [transitionDown_V]
      have h1 : transitionUpAway t (algebraMap _ _ (U t)) *
          transitionUpAway t (IsLocalization.Away.invSelf (U t)) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      rw [transitionUpAway_algebraMap, transitionUp_U] at h1
      exact eq_of_mul_eq_one_of_mul_eq_one h1 (IsLocalization.Away.mul_invSelf (V t))

/-- The two localizations of the crossing quotient identified by the chart transition. -/
def transitionEquiv : Localization.Away (U t) ≃+* OverlapRing t :=
  RingEquiv.ofRingHom (transitionUpAway t) (transitionDownAway t)
    (transitionUpAway_comp_transitionDownAway t) (transitionDownAway_comp_transitionUpAway t)

theorem toRingHom_transitionEquiv_comp :
    (transitionEquiv t).toRingHom.comp
        (algebraMap (CrossingQuotient W t) (Localization.Away (U t))) =
      (transitionUp t).toRingHom :=
  transitionUpAway_comp_algebraMap t

end transition

section spectra

/-- The affine crossing scheme `Spec (W[X, Y] / (X * Y - s))`. -/
abbrev crossingScheme (s : W) : Scheme.{u} := Spec (CommRingCat.of (CrossingQuotient W s))

abbrev chartScheme : Scheme.{u} := crossingScheme t

abbrev overlapScheme : Scheme.{u} := Spec (CommRingCat.of (OverlapRing t))

abbrev torusScheme : Scheme.{u} := Spec (CommRingCat.of (TorusRing t))

abbrev overlapToChartLeft : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (OverlapRing t)))

abbrev overlapToChartRight : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (transitionUp t).toRingHom)

abbrev torusToChart (i : ℕ) : torusScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (torusChart t i).toRingHom)

abbrev torusToOverlap (i : ℕ) : torusScheme t ⟶ overlapScheme t :=
  Spec.map (CommRingCat.ofHom (torusOverlap t i).toRingHom)

instance isOpenImmersion_overlapToChartRight : IsOpenImmersion (overlapToChartRight t) := by
  have H : IsIso (CommRingCat.ofHom (transitionEquiv t).toRingHom) :=
    inferInstanceAs (IsIso (transitionEquiv t).toCommRingCatIso.hom)
  rw [overlapToChartRight, ← toRingHom_transitionEquiv_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem isIso_ofHom_twistEquiv (i : ℕ) :
    IsIso (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) :=
  inferInstanceAs (IsIso (twistEquiv t i).toRingEquiv.toCommRingCatIso.hom)

theorem torusToChart_eq (i : ℕ) : torusToChart t i =
    Spec.map (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (TorusRing t))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem torusToOverlap_eq (i : ℕ) : torusToOverlap t i =
    Spec.map (CommRingCat.ofHom (twistEquiv t i).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (OverlapRing t) (TorusRing t))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

instance isOpenImmersion_torusToChart (i : ℕ) : IsOpenImmersion (torusToChart t i) := by
  have := isIso_ofHom_twistEquiv t i
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (TorusRing t)))) :=
    IsOpenImmersion.of_isLocalization (algebraMap W (CrossingQuotient W t) t)
  rw [torusToChart_eq]
  infer_instance

instance isOpenImmersion_torusToOverlap (i : ℕ) : IsOpenImmersion (torusToOverlap t i) := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToOverlap_eq]
  infer_instance

theorem torusToOverlap_overlapToChartLeft (i : ℕ) :
    torusToOverlap t i ≫ overlapToChartLeft t = torusToChart t i := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusOverlap_comp_toAlgHom t i))

theorem torusToOverlap_overlapToChartRight (i : ℕ) :
    torusToOverlap t i ≫ overlapToChartRight t = torusToChart t (i + 1) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusOverlap_comp_transitionUp t i))

theorem V_notMem_of_mem_range_overlapToChartLeft {P : chartScheme t}
    (hP : P ∈ Set.range (overlapToChartLeft t)) : V t ∉ P.asIdeal := by
  obtain ⟨Q, rfl⟩ := hP
  intro h
  have hu : IsUnit (algebraMap (CrossingQuotient W t) (OverlapRing t) (V t)) :=
    IsLocalization.Away.algebraMap_isUnit (V t)
  exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem U_notMem_of_mem_range_overlapToChartRight {P : chartScheme t}
    (hP : P ∈ Set.range (overlapToChartRight t)) : U t ∉ P.asIdeal := by
  obtain ⟨Q, rfl⟩ := hP
  intro h
  have hu : IsUnit ((transitionUp t).toRingHom (U t)) := by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U]
    exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V t))
  exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem mem_range_torusToChart {P : chartScheme t} (hU : U t ∉ P.asIdeal) (hV : V t ∉ P.asIdeal)
    (i : ℕ) : P ∈ Set.range (torusToChart t i) := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToChart_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]
  change P ∈ Set.range (PrimeSpectrum.comap (algebraMap (CrossingQuotient W t) (TorusRing t)))
  rw [PrimeSpectrum.localization_away_comap_range (TorusRing t)
    (algebraMap W (CrossingQuotient W t) t)]
  change algebraMap W (CrossingQuotient W t) t ∉ P.asIdeal
  rw [← U_mul_V]
  exact fun h => (P.isPrime.mem_or_mem h).elim hU hV

end spectra

/-- Index category for gluing the resolution: charts, overlaps of adjacent charts
and the common torus. -/
inductive GlueIndex (e : ℕ) : Type
  | chart (i : Fin e) : GlueIndex e
  | overlap (i : Fin e) (h : (i : ℕ) + 1 < e) : GlueIndex e
  | torus (h : 0 < e) : GlueIndex e

namespace GlueIndex

variable {e : ℕ}

protected def le : GlueIndex e → GlueIndex e → Prop
  | torus _, _ => True
  | overlap i _, overlap j _ => i = j
  | overlap i _, chart j => j = i ∨ (j : ℕ) = i + 1
  | chart i, chart j => i = j
  | overlap _ _, torus _ => False
  | chart _, torus _ => False
  | chart _, overlap _ _ => False

instance : LE (GlueIndex e) := ⟨GlueIndex.le⟩

@[simp] theorem torus_le (h : 0 < e) (b : GlueIndex e) : torus h ≤ b ↔ True := Iff.rfl
@[simp] theorem overlap_le_overlap (i j : Fin e) (h : (i : ℕ) + 1 < e) (h' : (j : ℕ) + 1 < e) :
    overlap i h ≤ overlap j h' ↔ i = j := Iff.rfl
@[simp] theorem overlap_le_chart (i j : Fin e) (h : (i : ℕ) + 1 < e) :
    overlap i h ≤ chart j ↔ j = i ∨ (j : ℕ) = i + 1 := Iff.rfl
@[simp] theorem chart_le_chart (i j : Fin e) : chart i ≤ chart j ↔ i = j := Iff.rfl
@[simp] theorem overlap_le_torus (i : Fin e) (h : (i : ℕ) + 1 < e) (h' : 0 < e) :
    overlap i h ≤ torus h' ↔ False := Iff.rfl
@[simp] theorem chart_le_torus (i : Fin e) (h' : 0 < e) : chart i ≤ torus h' ↔ False := Iff.rfl
@[simp] theorem chart_le_overlap (i j : Fin e) (h : (j : ℕ) + 1 < e) :
    chart i ≤ overlap j h ↔ False := Iff.rfl

instance : Preorder (GlueIndex e) where
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
        chart_le_torus, chart_le_overlap] at hab hbc ⊢ <;> subst_vars <;> simp_all

end GlueIndex

open GlueIndex

section diagram

variable (e : ℕ)

/-- The affine scheme attached to an index of the gluing diagram. -/
def glueObj : GlueIndex e → Scheme.{u}
  | .chart _ => chartScheme t
  | .overlap _ _ => overlapScheme t
  | .torus _ => torusScheme t

/-- The open immersions between the pieces of the gluing diagram. -/
def glueMap : ∀ a b : GlueIndex e, a ≤ b → (glueObj t e a ⟶ glueObj t e b)
  | .torus _, .torus _, _ => 𝟙 _
  | .torus _, .overlap i _, _ => torusToOverlap t i
  | .torus _, .chart j, _ => torusToChart t j
  | .overlap _ _, .overlap _ _, _ => 𝟙 _
  | .overlap i _, .chart j, _ =>
      if (j : ℕ) = i then overlapToChartLeft t else overlapToChartRight t
  | .chart _, .chart _, _ => 𝟙 _
  | .overlap _ _, .torus _, h => False.elim h
  | .chart _, .torus _, h => False.elim h
  | .chart _, .overlap _ _, h => False.elim h

@[simp] theorem glueMap_torus_torus (h h' : 0 < e) (hle) :
    glueMap t e (torus h) (torus h') hle = 𝟙 _ := rfl
@[simp] theorem glueMap_torus_overlap (h : 0 < e) (i : Fin e) (hi) (hle) :
    glueMap t e (torus h) (overlap i hi) hle = torusToOverlap t i := rfl
@[simp] theorem glueMap_torus_chart (h : 0 < e) (j : Fin e) (hle) :
    glueMap t e (torus h) (chart j) hle = torusToChart t j := rfl
@[simp] theorem glueMap_overlap_overlap (i j : Fin e) (hi hj) (hle) :
    glueMap t e (overlap i hi) (overlap j hj) hle = 𝟙 (overlapScheme t) := rfl
@[simp] theorem glueMap_chart_chart (i j : Fin e) (hle) :
    glueMap t e (chart i) (chart j) hle = 𝟙 (chartScheme t) := rfl
theorem glueMap_overlap_chart_self (i : Fin e) (hi) (hle) :
    glueMap t e (overlap i hi) (chart i) hle = overlapToChartLeft t := ite_eq_left rfl
theorem glueMap_overlap_chart_succ (i : Fin e) (hi) (hle) :
    glueMap t e (overlap i hi) (chart ⟨(i : ℕ) + 1, hi⟩) hle = overlapToChartRight t :=
  ite_eq_right (Nat.succ_ne_self _)
theorem glueMap_overlap_chart_of_eq {i j : Fin e} (hi) (hle) (h : (j : ℕ) = i) :
    glueMap t e (overlap i hi) (chart j) hle = overlapToChartLeft t := ite_eq_left h
theorem glueMap_overlap_chart_of_ne {i j : Fin e} (hi) (hle) (h : (j : ℕ) ≠ i) :
    glueMap t e (overlap i hi) (chart j) hle = overlapToChartRight t := ite_eq_right h

theorem glueMap_id (a : GlueIndex e) : glueMap t e a a le_rfl = 𝟙 _ := by
  cases a <;> rfl

theorem glueMap_comp (a b c : GlueIndex e) (hab : a ≤ b) (hbc : b ≤ c) :
    glueMap t e a c (hab.trans hbc) = glueMap t e a b hab ≫ glueMap t e b c hbc := by
  cases a <;> cases b <;> cases c <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab hbc
  all_goals (try subst_vars)
  case torus.overlap.chart =>
    rename_i he i hi hab0 j hbc0
    rcases hbc with rfl | hj
    · rw [glueMap_torus_chart, glueMap_torus_overlap, glueMap_overlap_chart_self]
      exact (torusToOverlap_overlapToChartLeft t j).symm
    · rw [glueMap_torus_chart, glueMap_torus_overlap, glueMap_overlap_chart_of_ne t e hi hbc0
        (by omega), hj]
      exact (torusToOverlap_overlapToChartRight t i).symm
  all_goals rfl

/-- The diagram of open immersions whose colimit is the resolution. -/
def glueDiagram : GlueIndex e ⥤ Scheme.{u} where
  obj := glueObj t e
  map f := glueMap t e _ _ f.le
  map_id a := glueMap_id t e a
  map_comp f g := glueMap_comp t e _ _ _ f.le g.le

@[simp] theorem glueDiagram_obj (a : GlueIndex e) : (glueDiagram t e).obj a = glueObj t e a := rfl

theorem glueDiagram_map {a b : GlueIndex e} (f : a ⟶ b) :
    (glueDiagram t e).map f = glueMap t e a b f.le := rfl

instance isOpenImmersion_glueMap (a b : GlueIndex e) (hab : a ≤ b) :
    IsOpenImmersion (glueMap t e a b hab) := by
  cases a <;> cases b <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab
  case overlap.chart =>
    rename_i i hi j hab0
    by_cases h : (j : ℕ) = i
    · rw [glueMap_overlap_chart_of_eq t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartLeft t))
    · rw [glueMap_overlap_chart_of_ne t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartRight t))
  case torus.torus => exact inferInstanceAs (IsOpenImmersion (𝟙 (torusScheme t)))
  case torus.overlap h i hi hab0 => exact inferInstanceAs (IsOpenImmersion (torusToOverlap t i))
  case torus.chart h j hab0 => exact inferInstanceAs (IsOpenImmersion (torusToChart t j))
  case overlap.overlap => exact inferInstanceAs (IsOpenImmersion (𝟙 (overlapScheme t)))
  case chart.chart => exact inferInstanceAs (IsOpenImmersion (𝟙 (chartScheme t)))

instance isOpenImmersion_glueDiagram_map {a b : GlueIndex e} (f : a ⟶ b) :
    IsOpenImmersion ((glueDiagram t e).map f) :=
  isOpenImmersion_glueMap t e a b f.le

end diagram

section locallyDirected

variable (e : ℕ)

theorem exists_of_mem_range_map {J : Type*} [Category J] [Quiver.IsThin J] (F : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    {i j k : J} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j)
    (h : F.map fi xi = F.map fj xj) (l : J) (fli : l ⟶ i) (flj : l ⟶ j)
    (hz : F.map fi xi ∈ Set.range (F.map (fli ≫ fi))) :
    ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : F.obj l), F.map fli x = xi ∧ F.map flj x = xj := by
  obtain ⟨z, hz⟩ := hz
  refine ⟨l, fli, flj, z, ?_, ?_⟩
  · apply (F.map fi).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hz]
  · apply (F.map fj).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, Subsingleton.elim (flj ≫ fj) (fli ≫ fi), hz, h]

variable {e}

theorem glue_cond_of_hom {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c) (hab : a ⟶ b)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb :=
  exists_of_mem_range_map (glueDiagram t e) fa fb xa xb h a (𝟙 a) hab
    ⟨xa, by rw [Category.id_comp]⟩

theorem glue_cond_of_hom' {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c) (hba : b ⟶ a)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb := by
  obtain ⟨l, flb, fla, x, hxb, hxa⟩ := glue_cond_of_hom t fb fa hba xb xa h.symm
  exact ⟨l, fla, flb, x, hxa, hxb⟩

theorem glue_cond {a b c : GlueIndex e} (fa : a ⟶ c) (fb : b ⟶ c)
    (xa : (glueDiagram t e).obj a) (xb : (glueDiagram t e).obj b)
    (h : (glueDiagram t e).map fa xa = (glueDiagram t e).map fb xb) :
    ∃ (l : GlueIndex e) (fla : l ⟶ a) (flb : l ⟶ b) (x : (glueDiagram t e).obj l),
      (glueDiagram t e).map fla x = xa ∧ (glueDiagram t e).map flb x = xb := by
  have hac := fa.le
  have hbc := fb.le
  cases c with
  | torus hc =>
    cases a <;> cases b <;> first
      | simp only [overlap_le_torus, chart_le_torus] at hac
      | simp only [overlap_le_torus, chart_le_torus] at hbc
      | exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
  | overlap k hk =>
    cases a with
    | chart _ => simp only [chart_le_overlap] at hac
    | torus _ => exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
    | overlap i hi =>
      cases b with
      | chart _ => simp only [chart_le_overlap] at hbc
      | torus _ => exact glue_cond_of_hom' t fa fb (homOfLE trivial) xa xb h
      | overlap j hj =>
        simp only [overlap_le_overlap] at hac hbc
        subst hac; subst hbc
        exact glue_cond_of_hom t fa fb (homOfLE (by simp)) xa xb h
  | chart k =>
    cases a with
    | torus _ => exact glue_cond_of_hom t fa fb (homOfLE trivial) xa xb h
    | chart i =>
      simp only [chart_le_chart] at hac
      subst hac
      exact glue_cond_of_hom' t fa fb fb xa xb h
    | overlap i hi =>
      cases b with
      | torus _ => exact glue_cond_of_hom' t fa fb (homOfLE trivial) xa xb h
      | chart j =>
        simp only [chart_le_chart] at hbc
        subst hbc
        exact glue_cond_of_hom t fa fb fa xa xb h
      | overlap j hj =>
        by_cases hij : i = j
        · subst hij
          exact glue_cond_of_hom t fa fb (homOfLE (by simp)) xa xb h
        · simp only [overlap_le_chart] at hac hbc
          have hUV : U t ∉ ((glueDiagram t e).map fa xa).asIdeal ∧
              V t ∉ ((glueDiagram t e).map fa xa).asIdeal := by
            rcases hac with hk | hk <;> rcases hbc with hk' | hk'
            · exact absurd (hk.symm.trans hk') hij
            · refine ⟨?_, ?_⟩
              · rw [h]
                refine U_notMem_of_mem_range_overlapToChartRight t ⟨xb, ?_⟩
                rw [show (glueDiagram t e).map fb = overlapToChartRight t from
                  glueMap_overlap_chart_of_ne t e hj fb.le (by omega)]
                rfl
              · refine V_notMem_of_mem_range_overlapToChartLeft t ⟨xa, ?_⟩
                rw [show (glueDiagram t e).map fa = overlapToChartLeft t from
                  glueMap_overlap_chart_of_eq t e hi fa.le (by rw [hk])]
                rfl
            · refine ⟨?_, ?_⟩
              · refine U_notMem_of_mem_range_overlapToChartRight t ⟨xa, ?_⟩
                rw [show (glueDiagram t e).map fa = overlapToChartRight t from
                  glueMap_overlap_chart_of_ne t e hi fa.le (by omega)]
                rfl
              · rw [h]
                refine V_notMem_of_mem_range_overlapToChartLeft t ⟨xb, ?_⟩
                rw [show (glueDiagram t e).map fb = overlapToChartLeft t from
                  glueMap_overlap_chart_of_eq t e hj fb.le (by rw [hk'])]
                rfl
            · exact absurd (Fin.ext (by omega)) hij
          exact exists_of_mem_range_map (glueDiagram t e) fa fb xa xb h (torus k.pos)
            (homOfLE trivial) (homOfLE trivial) (mem_range_torusToChart t hUV.1 hUV.2 k)

instance isLocallyDirected_glueDiagram : (glueDiagram t e ⋙ Scheme.forget).IsLocallyDirected where
  cond fa fb xa xb h := glue_cond t fa fb xa xb h

end locallyDirected

section scheme

variable (e : ℕ)

/-- The resolution of the crossing `X * Y = t ^ e`, glued from `e` copies of
the crossing `X * Y = t`. -/
def Resolution : Scheme.{u} := colimit (glueDiagram t e)

namespace Resolution

/-- The inclusion of the `i`-th chart into the resolution. -/
def ι (i : Fin e) : chartScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (chart i)

def ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) : overlapScheme t ⟶ Resolution t e :=
  colimit.ι (glueDiagram t e) (overlap i hi)

def ιTorus (h : 0 < e) : torusScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (torus h)

instance isOpenImmersion_ι (i : Fin e) : IsOpenImmersion (ι t e i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (chart i)))

instance isOpenImmersion_ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsOpenImmersion (ιOverlap t e i hi) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (overlap i hi)))

instance isOpenImmersion_ιTorus (h : 0 < e) : IsOpenImmersion (ιTorus t e h) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (torus h)))

@[reassoc]
theorem overlapToChartLeft_ι (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartLeft t ≫ ι t e i = ιOverlap t e i hi := by
  rw [← glueMap_overlap_chart_self t e i hi (by simp)]
  exact colimit.w (glueDiagram t e) (homOfLE (by simp) : overlap i hi ⟶ chart i)

@[reassoc]
theorem overlapToChartRight_ι (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartRight t ≫ ι t e ⟨(i : ℕ) + 1, hi⟩ = ιOverlap t e i hi := by
  rw [← glueMap_overlap_chart_succ t e i hi (by simp)]
  exact colimit.w (glueDiagram t e) (homOfLE (by simp) : overlap i hi ⟶ chart ⟨(i : ℕ) + 1, hi⟩)

@[reassoc]
theorem torusToChart_ι (i : Fin e) :
    torusToChart t i ≫ ι t e i = ιTorus t e i.pos :=
  colimit.w (glueDiagram t e) (homOfLE trivial : torus i.pos ⟶ chart i)

@[reassoc]
theorem torusToOverlap_ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    torusToOverlap t i ≫ ιOverlap t e i hi = ιTorus t e i.pos :=
  colimit.w (glueDiagram t e) (homOfLE trivial : torus i.pos ⟶ overlap i hi)

theorem glue_condition (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartLeft t ≫ ι t e i = overlapToChartRight t ≫ ι t e ⟨(i : ℕ) + 1, hi⟩ := by
  rw [overlapToChartLeft_ι, overlapToChartRight_ι]

set_option backward.isDefEq.respectTransparency.types false in
theorem exists_ι_apply_eq (x : Resolution t e) :
    ∃ (i : Fin e) (y : chartScheme t), ι t e i y = x := by
  obtain ⟨a, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (glueDiagram t e) x
  cases a with
  | chart i => exact ⟨i, y, hy⟩
  | overlap i hi =>
    refine ⟨i, overlapToChartLeft t y, ?_⟩
    rw [← Scheme.Hom.comp_apply, overlapToChartLeft_ι]
    exact hy
  | torus h =>
    refine ⟨⟨0, h⟩, torusToChart t ((⟨0, h⟩ : Fin e) : ℕ) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, torusToChart_ι]
    exact hy

theorem iSup_opensRange_ι : ⨆ i, (ι t e i).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

/-- The open cover of the resolution by its `e` charts. -/
def openCover : (Resolution t e).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin e) (fun _ => chartScheme t) (ι t e) (exists_ι_apply_eq t e)

@[simp] theorem openCover_I₀ : (openCover t e).I₀ = Fin e := rfl
@[simp] theorem openCover_X (i : Fin e) : (openCover t e).X i = chartScheme t := rfl
@[simp] theorem openCover_f (i : Fin e) : (openCover t e).f i = ι t e i := rfl

instance (i : (openCover t e).I₀) : IsAffine ((openCover t e).X i) :=
  inferInstanceAs (IsAffine (chartScheme t))

theorem ι_apply_eq_iff {i j : Fin e} (x y : chartScheme t) :
    ι t e i x = ι t e j y ↔ ∃ (a : GlueIndex e) (hi : a ≤ chart i) (hj : a ≤ chart j)
      (z : glueObj t e a), glueMap t e a (chart i) hi z = x ∧ glueMap t e a (chart j) hj z = y := by
  constructor
  · intro h
    obtain ⟨a, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueDiagram t e)).mp h
    exact ⟨a, fi.le, fj.le, z, h1, h2⟩
  · rintro ⟨a, hi, hj, z, h1, h2⟩
    exact (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueDiagram t e)).mpr
      ⟨a, homOfLE hi, homOfLE hj, z, h1, h2⟩

abbrev chartToCrossing (i : Fin e) : chartScheme t ⟶ crossingScheme (t ^ e) :=
  Spec.map (CommRingCat.ofHom (resolutionChart t e i).toRingHom)

def crossingCoconeApp : ∀ a : GlueIndex e, (glueObj t e a ⟶ crossingScheme (t ^ e))
  | .chart j => chartToCrossing t e j
  | .overlap i _ => overlapToChartLeft t ≫ chartToCrossing t e i
  | .torus h => torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, h⟩

theorem overlapToChartRight_chartToCrossing (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    overlapToChartRight t ≫ chartToCrossing t e ⟨(i : ℕ) + 1, hi⟩ =
      overlapToChartLeft t ≫ chartToCrossing t e i := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (congrArg AlgHom.toRingHom
    (?_ : (transitionUp t).comp (resolutionChart t e ⟨i + 1, hi⟩) =
      (IsScalarTower.toAlgHom W (CrossingQuotient W t) (OverlapRing t)).comp
          (resolutionChart t e i)))
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_U, resolutionChart_U, map_mul,
      map_mul, AlgHom.commutes, AlgHom.commutes, transitionUp_U]
    rw [pow_succ, map_mul,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (OverlapRing t) t,
      ← U_mul_V, map_mul, mul_assoc, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_V, resolutionChart_V, map_mul,
      map_mul, AlgHom.commutes, AlgHom.commutes, transitionUp_V]
    rw [← mul_assoc, ← map_mul, ← pow_succ,
      show e - 1 - ((i : ℕ) + 1) + 1 = e - 1 - (i : ℕ) by omega]
    rfl

theorem torusChart_comp_resolutionChart (i : Fin e) :
    (torusChart t i).comp (resolutionChart t e i) =
      (torusChart t 0).comp (resolutionChart t e ⟨0, i.pos⟩) := by
  apply algHom_ext_chart
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_U, resolutionChart_U, map_mul,
      map_mul,
      AlgHom.commutes, AlgHom.commutes, torusChart_U, torusChart_U, map_pow, map_pow]
    change tT t ^ (i : ℕ) * (xT t * tinv t ^ (i : ℕ)) = tT t ^ 0 * (xT t * tinv t ^ 0)
    rw [mul_left_comm, tT_pow_mul_tinv_pow, pow_zero, pow_zero, one_mul, mul_one]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, resolutionChart_V, resolutionChart_V, map_mul,
      map_mul,
      AlgHom.commutes, AlgHom.commutes, torusChart_V, torusChart_V, map_pow, map_pow]
    change tT t ^ (e - 1 - (i : ℕ)) * (yT t * tT t ^ (i : ℕ)) =
        tT t ^ (e - 1 - 0) * (yT t * tT t ^ 0)
    rw [mul_left_comm, ← pow_add, show e - 1 - (i : ℕ) + i = e - 1 - 0 by have := i.2; omega,
      pow_zero, mul_one, mul_comm]

theorem torusToChart_chartToCrossing (i : Fin e) :
    torusToChart t i ≫ chartToCrossing t e i =
      torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, i.pos⟩ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (congrArg AlgHom.toRingHom (torusChart_comp_resolutionChart t e i))

theorem glueMap_crossingCoconeApp (a b : GlueIndex e) (hab : a ≤ b) :
    glueMap t e a b hab ≫ crossingCoconeApp t e b = crossingCoconeApp t e a := by
  cases a <;> cases b <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab
  case torus.torus => exact Category.id_comp _
  case torus.overlap h i hi hab0 =>
    change torusToOverlap t i ≫ overlapToChartLeft t ≫ chartToCrossing t e i =
        torusToChart t (0 : ℕ) ≫ _
    rw [← Category.assoc, torusToOverlap_overlapToChartLeft, torusToChart_chartToCrossing]
  case torus.chart h j hab0 => exact torusToChart_chartToCrossing t e j
  case overlap.overlap => subst hab; exact Category.id_comp _
  case overlap.chart i hi j hab0 =>
    rcases hab with rfl | hj
    · rw [glueMap_overlap_chart_self]; rfl
    · obtain rfl : j = ⟨(i : ℕ) + 1, hi⟩ := Fin.ext hj
      rw [glueMap_overlap_chart_succ]
      exact overlapToChartRight_chartToCrossing t e i hi
  case chart.chart => subst hab; exact Category.id_comp _

def crossingCocone : Cocone (glueDiagram t e) where
  pt := crossingScheme (t ^ e)
  ι := { app := crossingCoconeApp t e
         naturality := fun a b f =>
           (glueMap_crossingCoconeApp t e a b f.le).trans (Category.comp_id _).symm }

/-- The resolution morphism to the crossing scheme of `t ^ e`. -/
def toCrossing : Resolution t e ⟶ crossingScheme (t ^ e) :=
  colimit.desc (glueDiagram t e) (crossingCocone t e)

@[reassoc (attr := simp)]
theorem ι_toCrossing (i : Fin e) : ι t e i ≫ toCrossing t e = chartToCrossing t e i :=
  colimit.ι_desc (crossingCocone t e) (chart i)

@[reassoc]
theorem ιTorus_toCrossing (h : 0 < e) :
    ιTorus t e h ≫ toCrossing t e = torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, h⟩ :=
  colimit.ι_desc (crossingCocone t e) (torus h)

/-- The structure morphism of the resolution to `Spec W`. -/
def toSpec : Resolution t e ⟶ Spec (CommRingCat.of W) :=
  toCrossing t e ≫ Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W (t ^ e))))

@[reassoc (attr := simp)]
theorem ι_toSpec (i : Fin e) :
    ι t e i ≫ toSpec t e = Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t))) := by
  rw [toSpec, ι_toCrossing_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (resolutionChart t e i).comp_algebraMap

theorem hom_ext {X : Scheme.{u}} {f g : Resolution t e ⟶ X} (h : ∀ i, ι t e i ≫ f = ι t e i ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro a
  cases a with
  | chart i => exact h i
  | overlap i hi =>
    change ιOverlap t e i hi ≫ f = ιOverlap t e i hi ≫ g
    rw [← overlapToChartLeft_ι, Category.assoc, Category.assoc, h i]
  | torus h0 =>
    change ιTorus t e h0 ≫ f = ιTorus t e h0 ≫ g
    rw [← torusToChart_ι t e ⟨0, h0⟩, Category.assoc, Category.assoc, h]

end Resolution

end scheme

end CrossingQuotient

end MvPolynomial

end

open MvPolynomial MvPolynomial.CrossingQuotient

namespace CrossingResolutionChartAux

private theorem exists_factor {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] :
    ∀ (n : ℕ) (a b c : O), a * b = c ^ (n + 1) →
      ∃ (i : ℕ) (x y : O), i ≤ n ∧ x * y = c ∧ a = c ^ i * x ∧ b = c ^ (n - i) * y := by
  intro n
  induction n with
  | zero =>
    intro a b c h
    exact ⟨0, a, b, le_rfl, by rw [h, zero_add, pow_one], by rw [pow_zero, one_mul],
      by rw [Nat.sub_zero, pow_zero, one_mul]⟩
  | succ n ih =>
    intro a b c h
    by_cases ha : a = 0
    · have hc : c = 0 := by
        rw [ha, zero_mul] at h
        exact eq_zero_of_pow_eq_zero h.symm
      refine ⟨n + 1, 0, b, le_rfl, ?_, ?_, ?_⟩
      · rw [zero_mul, hc]
      · rw [ha, mul_zero]
      · rw [Nat.sub_self, pow_zero, one_mul]
    obtain ⟨d, hd | hd⟩ := ValuationRing.cond c a
    · have hc : c ≠ 0 := by rintro rfl; rw [zero_mul] at hd; exact ha hd.symm
      have hdb : d * b = c ^ (n + 1) := by
        apply mul_left_cancel₀ hc
        rw [← mul_assoc, hd, h, pow_succ' c (n + 1)]
      obtain ⟨i, x, y, hi, hxy, hdx, hby⟩ := ih d b c hdb
      refine ⟨i + 1, x, y, by omega, hxy, ?_, ?_⟩
      · rw [← hd, hdx, pow_succ]; ring
      · rw [hby]; congr 2; omega
    · refine ⟨0, a, d, Nat.zero_le _, hd, by rw [pow_zero, one_mul], ?_⟩
      apply mul_left_cancel₀ ha
      rw [Nat.sub_zero, h, pow_succ, ← hd]; ring

variable {W : Type*} [CommRing W] (t : W)

private theorem mk_C_eq (s : W) (w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

private theorem exists_comp_resolutionChart_eq {e : ℕ} (he : 0 < e)
    {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (g : CrossingQuotient W (t ^ e) →+* O) :
    ∃ (i : Fin e) (g' : CrossingQuotient W t →+* O),
      g'.comp (resolutionChart t e i).toRingHom = g := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  set a : O := g (U (t ^ (n + 1))) with ha
  set b : O := g (V (t ^ (n + 1))) with hb
  set c : O := g (algebraMap W _ t) with hc
  have hct : ∀ m : ℕ, g (algebraMap W _ (t ^ m)) = c ^ m := fun m => by
    rw [hc, ← map_pow, ← map_pow]
  have hab : a * b = c ^ (n + 1) := by
    rw [ha, hb, ← map_mul, U_mul_V, hct]
  obtain ⟨i, x, y, hi, hxy, hax, hby⟩ := exists_factor n a b c hab
  let : Algebra W O := (g.comp (algebraMap W (CrossingQuotient W (t ^ (n + 1))))).toAlgebra
  have halg : ∀ w : W, algebraMap W O w = g (algebraMap W _ w) := fun w => rfl
  have hxy' : x * y = algebraMap W O t := by rw [halg, hxy]
  refine ⟨⟨i, by omega⟩, (CrossingQuotient.lift t x y hxy').toRingHom, ?_⟩
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change (CrossingQuotient.lift t x y hxy') (resolutionChart t (n + 1) ⟨i, _⟩ (mk _ (C w))) =
      g (mk _ (C w))
    rw [mk_C_eq, AlgHom.commutes, AlgHom.commutes, halg]
  · intro j
    fin_cases j
    · change (CrossingQuotient.lift t x y hxy') (resolutionChart t (n + 1) ⟨i, _⟩ (U (t ^ (n + 1))))
        = g (U (t ^ (n + 1)))
      rw [resolutionChart_U, map_mul, AlgHom.commutes, lift_U, halg, hct, ← ha, hax]
    · change (CrossingQuotient.lift t x y hxy') (resolutionChart t (n + 1) ⟨i, _⟩ (V (t ^ (n + 1))))
        = g (V (t ^ (n + 1)))
      rw [resolutionChart_V, map_mul, AlgHom.commutes, lift_V, halg, hct, ← hb, hby]
      congr 2

end CrossingResolutionChartAux

/-- A ring map from the crossing quotient of `t ^ e` to a valuation ring factors through
one of the resolution charts. -/
theorem MvPolynomial.CrossingQuotient.exists_comp_resolutionChart_eq_of_valuationRing
    {W : Type*} [CommRing W] (t : W) {e : ℕ} (he : 0 < e)
    {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (g : CrossingQuotient W (t ^ e) →+* O) :
    ∃ (i : Fin e) (g' : CrossingQuotient W t →+* O),
      g'.comp (resolutionChart t e i).toRingHom = g :=
  CrossingResolutionChartAux.exists_comp_resolutionChart_eq t he g

universe u2

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

namespace CrossingResolutionValuativeAux

variable {W : Type u2} [CommRing W]

section ring

variable {A : Type*} [CommRing A]

private theorem eval₂Hom_rel (s : W) (f : W →+* A) (a b : A) (h : a * b = f s) :
    eval₂Hom f ![a, b] (X 0 * X 1 - C s : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

private noncomputable def pointHom (s : W) (f : W →+* A) (a b : A) (h : a * b = f s) :
    CrossingQuotient W s →+* A :=
  Ideal.Quotient.lift (Ideal.span {(X 0 * X 1 - C s : MvPolynomial (Fin 2) W)}) (eval₂Hom f ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, eval₂Hom_rel s f a b h, mul_zero])

private theorem pointHom_mk (s : W) (f : W →+* A) (a b : A) (h : a * b = f s)
    (p : MvPolynomial (Fin 2) W) :
    pointHom s f a b h (mk s p) = eval₂Hom f ![a, b] p := rfl

private theorem pointHom_algebraMap (s : W) (f : W →+* A) (a b : A) (h : a * b = f s) (w : W) :
    pointHom s f a b h (algebraMap W _ w) = f w := by
  rw [← mk_C_eq_algebraMap, pointHom_mk, eval₂Hom_C]

private theorem pointHom_U (s : W) (f : W →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (U s) = a := by
  change pointHom s f a b h (mk s (X 0)) = a
  rw [pointHom_mk, eval₂Hom_X']
  rfl

private theorem pointHom_V (s : W) (f : W →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (V s) = b := by
  change pointHom s f a b h (mk s (X 1)) = b
  rw [pointHom_mk, eval₂Hom_X']
  rfl

private theorem _root_.CrossingResolutionValuativeAux.ringHom_ext {s : W} {f g : CrossingQuotient W
    s →+* A}
    (hW : ∀ w : W, f (algebraMap W _ w) = g (algebraMap W _ w))
    (hU : f (U s) = g (U s)) (hV : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change f (mk s (C w)) = g (mk s (C w))
    rw [mk_C_eq_algebraMap]
    exact hW w
  · intro j
    fin_cases j
    · exact hU
    · exact hV

private theorem ringHom_ext_of_U [IsDomain A] {s : W} {f g : CrossingQuotient W s →+* A}
    (hW : ∀ w : W, f (algebraMap W _ w) = g (algebraMap W _ w))
    (hU : f (U s) = g (U s)) (h0 : g (U s) ≠ 0) : f = g := by
  refine ringHom_ext hW hU (mul_left_cancel₀ h0 ?_)
  calc g (U s) * f (V s) = f (U s) * f (V s) := by rw [hU]
    _ = f (algebraMap W _ s) := by rw [← map_mul, U_mul_V]
    _ = g (algebraMap W _ s) := hW s
    _ = g (U s) * g (V s) := by rw [← map_mul, U_mul_V]

end ring

section glue

variable (t : W) (e : ℕ) {K : Type u2} [CommRing K]

private theorem specMap_ofHom_comp {A B D : Type u2} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

private theorem specMap_comp_ι_eq_of_torus (i j : Fin e) (χ : TorusRing t →+* K) :
    Spec.map (CommRingCat.ofHom (χ.comp (torusChart t i).toRingHom)) ≫ Resolution.ι t e i =
      Spec.map (CommRingCat.ofHom (χ.comp (torusChart t j).toRingHom)) ≫ Resolution.ι t e j := by
  rw [specMap_ofHom_comp, specMap_ofHom_comp, Category.assoc, Category.assoc]
  change Spec.map _ ≫ torusToChart t i ≫ _ = Spec.map _ ≫ torusToChart t j ≫ _
  rw [Resolution.torusToChart_ι, Resolution.torusToChart_ι]

private theorem specMap_comp_ι_eq_of_overlap (j : Fin e) (hj : (j : ℕ) + 1 < e)
    (ω : OverlapRing t →+* K) :
    Spec.map (CommRingCat.ofHom
        (ω.comp (algebraMap (CrossingQuotient W t) (OverlapRing t)))) ≫ Resolution.ι t e j =
      Spec.map (CommRingCat.ofHom (ω.comp (transitionUp t).toRingHom)) ≫
        Resolution.ι t e ⟨(j : ℕ) + 1, hj⟩ := by
  have h1 : Spec.map (CommRingCat.ofHom
      (ω.comp (algebraMap (CrossingQuotient W t) (OverlapRing t)))) =
      Spec.map (CommRingCat.ofHom ω) ≫ overlapToChartLeft t := specMap_ofHom_comp _ _
  have h2 : Spec.map (CommRingCat.ofHom (ω.comp (transitionUp t).toRingHom)) =
      Spec.map (CommRingCat.ofHom ω) ≫ overlapToChartRight t := specMap_ofHom_comp _ _
  rw [h1, h2, Category.assoc, Category.assoc, Resolution.glue_condition t e j hj]

end glue

section lift

variable (t : W) (e : ℕ)

private theorem specMap_cancel {R K : Type u2} [CommRing R] [CommRing K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    {B : CommRingCat.{u2}} {f g : Spec (CommRingCat.of R) ⟶ Spec B}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext x
  exact hinj (congrArg (fun k : B ⟶ CommRingCat.of K => k.hom x) h')

private theorem hasLift_of (S : ValuativeCommSq (Resolution.toCrossing t e)) (i j : Fin e)
    (φ : CrossingQuotient W t →+* S.K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Resolution.ι t e i = S.i₁)
    (φ' : CrossingQuotient W t →+* S.R)
    (hglue : Spec.map (CommRingCat.ofHom ((algebraMap S.R S.K).comp φ')) ≫ Resolution.ι t e j =
      Spec.map (CommRingCat.ofHom φ) ≫ Resolution.ι t e i) :
    S.commSq.HasLift := by
  have fac_left : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫
      Spec.map (CommRingCat.ofHom φ') ≫ Resolution.ι t e j = S.i₁ := by
    rw [← Category.assoc, ← specMap_ofHom_comp, hglue, hφ]
  refine CommSq.HasLift.mk' ⟨Spec.map (CommRingCat.ofHom φ') ≫ Resolution.ι t e j, fac_left, ?_⟩
  apply specMap_cancel (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, fac_left]
  exact S.commSq.w

end lift

section chart

variable (t : W) (e : ℕ)

private theorem exists_chart (S : ValuativeCommSq (Resolution.toCrossing t e)) :
    ∃ (i : Fin e) (φ : CrossingQuotient W t →+* S.K) (ψ : CrossingQuotient W (t ^ e) →+* S.R),
      Spec.map (CommRingCat.ofHom φ) ≫ Resolution.ι t e i = S.i₁ ∧
      Spec.map (CommRingCat.ofHom ψ) = S.i₂ ∧
      φ.comp (resolutionChart t e i).toRingHom = (algebraMap S.R S.K).comp ψ := by
  let p₀ : PrimeSpectrum S.K := default
  obtain ⟨i, y, hy⟩ := Resolution.exists_ι_apply_eq t e (S.i₁ p₀)
  have hrange : Set.range S.i₁ ⊆ Set.range (Resolution.ι t e i) := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum S.K) _ _
    exact ⟨y, hy⟩
  let g := IsOpenImmersion.lift (Resolution.ι t e i) S.i₁ hrange
  have hg : g ≫ Resolution.ι t e i = S.i₁ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨i, (Spec.preimage g).hom, (Spec.preimage S.i₂).hom, ?_, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hg
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  · have key : Spec.map (CommRingCat.ofHom
          ((Spec.preimage g).hom.comp (resolutionChart t e i).toRingHom)) =
        Spec.map (CommRingCat.ofHom ((algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom)) := by
      rw [specMap_ofHom_comp, specMap_ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
        Spec.map_preimage, Spec.map_preimage]
      change g ≫ Resolution.chartToCrossing t e i = _
      rw [← Resolution.ι_toCrossing, ← Category.assoc, hg]
      exact S.commSq.w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end chart

section main

private theorem main (t : W) (e : ℕ) : ValuativeCriterion.Existence
    (Resolution.toCrossing t e) := by
  intro S
  obtain ⟨i, φ, ψ, hφ, hψ, hcomm⟩ := exists_chart t e S
  have he : 0 < e := i.pos
  have hinj : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  obtain ⟨a, ha⟩ : ∃ a, φ (U t) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, φ (V t) = b := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, φ (algebraMap W _ t) = τ := ⟨_, rfl⟩
  have hab : a * b = τ := by rw [← ha, ← hb, ← map_mul, U_mul_V, hτ]
  have hτpow : ∀ m : ℕ, φ (algebraMap W _ (t ^ m)) = τ ^ m := fun m => by
    rw [map_pow, map_pow, hτ]
  have hcomm' : ∀ z, φ (resolutionChart t e i z) = algebraMap S.R S.K (ψ z) := fun z => by
    have := RingHom.congr_fun hcomm z
    rwa [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  have hσ : ∀ w : W, algebraMap S.R S.K (ψ (algebraMap W _ w)) = φ (algebraMap W _ w) := fun w => by
    rw [← hcomm', AlgHom.commutes]
  have hu : τ ^ (i : ℕ) * a = algebraMap S.R S.K (ψ (U (t ^ e))) := by
    rw [← hcomm', resolutionChart_U, map_mul, hτpow, ha]
  have hv : τ ^ (e - 1 - (i : ℕ)) * b = algebraMap S.R S.K (ψ (V (t ^ e))) := by
    rw [← hcomm', resolutionChart_V, map_mul, hτpow, hb]
  by_cases hτ0 : τ = 0
  · have hψt : ψ (algebraMap W _ t) = 0 :=
      hinj (by rw [hσ, hτ, hτ0, map_zero])
    have hψW : ∀ w : W, (ψ.comp (algebraMap W (CrossingQuotient W (t ^ e)))) w =
        ψ (algebraMap W _ w) := fun w => rfl
    by_cases haO : IsLocalization.IsInteger S.R a
    · obtain ⟨a', ha'⟩ := haO
      by_cases hbO : IsLocalization.IsInteger S.R b
      · obtain ⟨b', hb'⟩ := hbO
        have hrel : a' * b' = (ψ.comp (algebraMap W (CrossingQuotient W (t ^ e)))) t := by
          rw [hψW, hψt]
          apply hinj
          rw [map_mul, ha', hb', hab, hτ0, map_zero]
        let φ' : CrossingQuotient W t →+* S.R := pointHom t _ a' b' hrel
        have hA : (algebraMap S.R S.K).comp φ' = φ := by
          apply ringHom_ext
          · intro w
            rw [RingHom.comp_apply, pointHom_algebraMap, hψW, hσ]
          · rw [RingHom.comp_apply, pointHom_U, ha', ha]
          · rw [RingHom.comp_apply, pointHom_V, hb', hb]
        exact hasLift_of t e S i i φ hφ φ' (by rw [hA])
      · have hb0 : b ≠ 0 := by
          rintro rfl
          exact hbO ⟨0, by rw [map_zero]⟩
        obtain ⟨c, hc⟩ : IsLocalization.IsInteger S.R b⁻¹ :=
          (ValuationRing.isInteger_or_isInteger S.R b).resolve_left hbO
        have ha0 : a = 0 := by
          have h := hab.trans hτ0
          exact (mul_eq_zero.mp h).resolve_right hb0
        have hi : (i : ℕ) + 1 < e := by
          by_contra hi
          have h0 : e - 1 - (i : ℕ) = 0 := by omega
          rw [h0, pow_zero, one_mul] at hv
          exact hbO ⟨_, hv.symm⟩
        have hrel : c * 0 = (ψ.comp (algebraMap W (CrossingQuotient W (t ^ e)))) t := by
          rw [mul_zero, hψW, hψt]
        let φ' : CrossingQuotient W t →+* S.R := pointHom t _ c 0 hrel
        have hunit : IsUnit (φ (V t)) := by rw [hb]; exact isUnit_iff_ne_zero.mpr hb0
        let ω : OverlapRing t →+* S.K := IsLocalization.Away.lift (V t) hunit
        have hωC : ∀ z, ω (algebraMap (CrossingQuotient W t) (OverlapRing t) z) = φ z :=
          fun z => IsLocalization.Away.lift_eq (V t) hunit z
        have hωl : ω.comp (algebraMap (CrossingQuotient W t) (OverlapRing t)) = φ :=
          IsLocalization.Away.lift_comp (V t) hunit
        have hωr : ω.comp (transitionUp t).toRingHom = (algebraMap S.R S.K).comp φ' := by
          apply ringHom_ext_of_U
          · intro w
            rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
              IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (OverlapRing t), hωC, ← hσ,
              RingHom.comp_apply, pointHom_algebraMap]
            rfl
          · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U,
              RingHom.comp_apply, pointHom_U, hc]
            have h1 : ω (algebraMap _ _ (V t)) * ω (IsLocalization.Away.invSelf (V t)) = 1 := by
              rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
            rw [hωC, hb] at h1
            exact (inv_eq_of_mul_eq_one_right h1).symm
          · rw [RingHom.comp_apply, pointHom_U, hc]
            exact inv_ne_zero hb0
        refine hasLift_of t e S i ⟨(i : ℕ) + 1, hi⟩ φ hφ φ' ?_
        rw [← hωr, ← hωl]
        exact (specMap_comp_ι_eq_of_overlap t e i hi ω).symm
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact haO ⟨0, by rw [map_zero]⟩
      obtain ⟨c, hc⟩ : IsLocalization.IsInteger S.R a⁻¹ :=
        (ValuationRing.isInteger_or_isInteger S.R a).resolve_left haO
      have hb0 : b = 0 := by
        have h := hab.trans hτ0
        exact (mul_eq_zero.mp h).resolve_left ha0
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (i : ℕ) = k + 1 := by
        refine ⟨(i : ℕ) - 1, ?_⟩
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
        · rw [h0, pow_zero, one_mul] at hu
          exact absurd ⟨_, hu.symm⟩ haO
        · omega
      have hk' : k + 1 < e := hk ▸ i.2
      obtain rfl : i = ⟨k + 1, hk'⟩ := Fin.ext hk
      have hke : k < e := by omega
      have hrel : 0 * c = (ψ.comp (algebraMap W (CrossingQuotient W (t ^ e)))) t := by
        rw [zero_mul, hψW, hψt]
      let φ' : CrossingQuotient W t →+* S.R := pointHom t _ 0 c hrel
      have hunit : IsUnit (((algebraMap S.R S.K).comp φ') (V t)) := by
        rw [RingHom.comp_apply, pointHom_V, hc]
        exact isUnit_iff_ne_zero.mpr (inv_ne_zero ha0)
      let ω : OverlapRing t →+* S.K := IsLocalization.Away.lift (V t) hunit
      have hωC : ∀ z, ω (algebraMap (CrossingQuotient W t) (OverlapRing t) z) =
          algebraMap S.R S.K (φ' z) :=
        fun z => IsLocalization.Away.lift_eq (V t) hunit z
      have hωl : ω.comp (algebraMap (CrossingQuotient W t) (OverlapRing t)) =
          (algebraMap S.R S.K).comp φ' :=
        IsLocalization.Away.lift_comp (V t) hunit
      have hωr : ω.comp (transitionUp t).toRingHom = φ := by
        apply ringHom_ext_of_U
        · intro w
          rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
            IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (OverlapRing t), hωC,
            pointHom_algebraMap, ← hσ]
          rfl
        · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U, ha]
          have h1 : ω (algebraMap _ _ (V t)) * ω (IsLocalization.Away.invSelf (V t)) = 1 := by
            rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
          rw [hωC, pointHom_V, hc] at h1
          exact ((inv_mul_eq_one₀ ha0).mp h1).symm
        · rw [ha]
          exact ha0
      refine hasLift_of t e S ⟨k + 1, hk'⟩ ⟨k, hke⟩ φ hφ φ' ?_
      rw [← hωr, ← hωl]
      exact specMap_comp_ι_eq_of_overlap t e ⟨k, hke⟩ hk' ω
  · obtain ⟨j, g', hg'⟩ := exists_comp_resolutionChart_eq_of_valuationRing t he ψ
    have hg'' : ∀ z, g' (resolutionChart t e j z) = ψ z := fun z => by
      have := RingHom.congr_fun hg' z
      rwa [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    have hφt : IsUnit (φ (algebraMap W (CrossingQuotient W t) t)) := by
      rw [hτ]; exact isUnit_iff_ne_zero.mpr hτ0
    let φT : TorusRing t →+* S.K :=
      IsLocalization.Away.lift (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t) hφt
    have hφT : ∀ z, φT (algebraMap (CrossingQuotient W t) (TorusRing t) z) = φ z :=
      fun z => IsLocalization.Away.lift_eq (S := TorusRing t) _ hφt z
    have hφTt : φT (tT t) = τ := by
      change φT (algebraMap W (TorusRing t) t) = τ
      rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t), hφT, hτ]
    have hφTtinv : φT (tinv t) = τ⁻¹ := by
      have h1 : φT (tT t) * φT (tinv t) = 1 := by rw [← map_mul, tT_mul_tinv, map_one]
      rw [hφTt] at h1
      exact (inv_eq_of_mul_eq_one_right h1).symm
    let χ : TorusRing t →+* S.K := φT.comp (twistEquiv t (i : ℕ)).symm.toAlgHom.toRingHom
    have hχ_apply : ∀ z, χ z = φT ((twistEquiv t (i : ℕ)).symm z) := fun z => rfl
    have hχi : χ.comp (torusChart t i).toRingHom = φ := by
      refine RingHom.ext fun z => ?_
      change φT ((twistEquiv t (i : ℕ)).symm (twistEquiv t (i : ℕ)
        (algebraMap (CrossingQuotient W t) (TorusRing t) z))) = φ z
      rw [AlgEquiv.symm_apply_apply, hφT]
    have hχW : ∀ w : W, χ (algebraMap W (TorusRing t) w) = φ (algebraMap W _ w) := fun w => by
      rw [hχ_apply, AlgEquiv.commutes,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t), hφT]
    have hχtinv : χ (tinv t) = τ⁻¹ := by
      have h1 : χ (tinv t) * χ (tT t) = 1 := by rw [← map_mul, tinv_mul_tT, map_one]
      have h2 : χ (tT t) = τ := by rw [← hτ]; exact hχW t
      rw [h2] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hχx : χ (xT t) = a * τ ^ (i : ℕ) := by
      rw [hχ_apply]
      change φT (twist t (tT t ^ (i : ℕ)) (tinv t ^ (i : ℕ)) (tT_pow_mul_tinv_pow t i) (xT t)) = _
      rw [twist_xT, map_mul, map_pow, hφT, ha, hφTt]
    have hσ' : ∀ w : W, algebraMap S.R S.K (g' (algebraMap W _ w)) = φ (algebraMap W _ w) :=
      fun w => by rw [← hσ, ← hg'', AlgHom.commutes]
    have hgu : τ ^ (j : ℕ) * algebraMap S.R S.K (g' (U t)) = τ ^ (i : ℕ) * a := by
      rw [hu, ← hg'', resolutionChart_U, map_mul, map_mul, map_pow, map_pow, map_pow, hσ' t, hτ]
    have hχj : χ.comp (torusChart t j).toRingHom = (algebraMap S.R S.K).comp g' := by
      apply ringHom_ext_of_U
      · intro w
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hχW,
          RingHom.comp_apply, hσ']
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, torusChart_U, map_mul,
          map_pow, hχx, hχtinv, RingHom.comp_apply]
        apply mul_left_cancel₀ (pow_ne_zero (j : ℕ) hτ0)
        rw [hgu, inv_pow, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero (j : ℕ) hτ0), mul_one,
          mul_comm]
      · intro h0
        rw [RingHom.comp_apply] at h0
        rw [h0, mul_zero] at hgu
        have ha0 : a = 0 := (mul_eq_zero.mp hgu.symm).resolve_left (pow_ne_zero _ hτ0)
        apply hτ0
        rw [← hab, ha0, zero_mul]
    refine hasLift_of t e S i j φ hφ g' ?_
    rw [← hχj, ← hχi]
    exact (specMap_comp_ι_eq_of_torus t e i j χ).symm

end main

end CrossingResolutionValuativeAux

/-- The resolution morphism satisfies the existence part of the valuative criterion. -/
theorem MvPolynomial.CrossingQuotient.Resolution.valuativeCriterion_existence_toCrossing
    {W : Type u2} [CommRing W] (t : W) (e : ℕ) :
    ValuativeCriterion.Existence (Resolution.toCrossing t e) :=
  CrossingResolutionValuativeAux.main t e

universe u3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MvPolynomial MvPolynomial.CrossingQuotient
open scoped TensorProduct

namespace CrossingResolutionSeparatedAux

variable {W : Type u3} [CommRing W] (t : W) (e : ℕ)

open MvPolynomial.CrossingQuotient.GlueIndex MvPolynomial.CrossingQuotient.Resolution

local notation "C₀" => CrossingQuotient W t
local notation "X₀" => Resolution t e

private theorem isClosedImmersion_mapDesc {A : Type u3} [CommRing A] [Algebra W A]
    (r₁ r₂ : C₀ →ₐ[W] A) (i j : Fin e)
    (h : IsPullback (Spec.map (CommRingCat.ofHom r₁.toRingHom))
      (Spec.map (CommRingCat.ofHom r₂.toRingHom)) (Resolution.ι t e i) (Resolution.ι t e j))
    (hφ : Function.Surjective
      (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] A)) :
    IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j)
        (toSpec t e)) := by
  let φ : C₀ ⊗[W] C₀ →ₐ[W] A := Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)
  let f := CommRingCat.ofHom (R := C₀ ⊗[W] C₀) (S := A) φ.toRingHom
  have hφ' : Function.Surjective f.hom := hφ
  have hcl : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f hφ'
  have hleft : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := C₀) (S := C₀ ⊗[W] C₀)
      Algebra.TensorProduct.includeLeftRingHom) = Spec.map (CommRingCat.ofHom r₁.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft r₁ r₂
      (fun _ _ => Commute.all _ _) :
        (φ.restrictScalars W).comp Algebra.TensorProduct.includeLeft = r₁)
  have hright : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := C₀) (S := C₀ ⊗[W] C₀)
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := W) (A := C₀) (B := C₀)))) =
      Spec.map (CommRingCat.ofHom r₂.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight r₁ r₂
      (fun _ _ => Commute.all _ _) : φ.comp Algebra.TensorProduct.includeRight = r₂)
  let ε := pullback.congrHom (ι_toSpec t e i) (ι_toSpec t e j)
  have key : pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e) =
      h.isoPullback.inv ≫ Spec.map f ≫
        (pullbackSpecIso W (CrossingQuotient W t) (CrossingQuotient W t)).inv ≫ ε.inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_fst, Category.comp_id, pullbackSpecIso_inv_fst,
        hleft, h.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_snd, Category.comp_id, pullbackSpecIso_inv_snd,
        hright, h.isoPullback_inv_snd]
  rw [key]
  infer_instance

private abbrev Qci : AffineTargetMorphismProperty := fun X _ f _ ↦ IsAffine X ∧ Function.Surjective
    f.appTop

set_option backward.isDefEq.respectTransparency.types false in
private theorem isSeparated_of_blocks
    (hblock : ∀ i j : Fin e,
      IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e))) :
    IsSeparated (toSpec t e) := by
  have : Qci.IsLocal := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  have hQ : Qci.diagonal (toSpec t e) :=
    AffineTargetMorphismProperty.diagonal_of_openCover_source (Q := Qci) (toSpec t e)
      (Resolution.openCover t e) fun i j =>
        (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp (hblock i j)
  exact ⟨(HasAffineProperty.diagonal_iff (P := @IsClosedImmersion) (f := toSpec t e)).mp hQ⟩

section squares

variable {t e}

private theorem preimage_opensRange_eq {U : Scheme.{u3}} (g : U ⟶ chartScheme t) [IsOpenImmersion g]
    (i j : Fin e)
    (hout : ∀ (P : chartScheme t) (Q : chartScheme t),
      Resolution.ι t e i Q = Resolution.ι t e j P → P ∈ Set.range g)
    (hin : ∀ z : U, ∃ Q : chartScheme t, Resolution.ι t e i Q = Resolution.ι t e j (g z)) :
    Resolution.ι t e j ⁻¹ᵁ (Resolution.ι t e i).opensRange = g.opensRange := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ⟩ := hP
    exact hout P Q hQ
  · rintro ⟨z, rfl⟩
    exact hin z

set_option backward.isDefEq.respectTransparency.types false in
private theorem isPullback_overlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsPullback (overlapToChartLeft t) (overlapToChartRight t)
      (Resolution.ι t e i) (Resolution.ι t e ⟨(i : ℕ) + 1, hi⟩) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (glue_condition t e i hi).symm ?_
  apply preimage_opensRange_eq
  · intro P Q hPQ
    obtain ⟨a, ha, hb, z, hza, hzb⟩ := (ι_apply_eq_iff t e Q P).mp hPQ
    cases a with
    | chart k =>
      simp only [chart_le_chart] at ha hb
      exact absurd (congrArg Fin.val (ha.symm.trans hb)) (by simp)
    | overlap k hk =>
      simp only [overlap_le_chart] at ha hb
      have hk' : k = i := by
        rcases ha with h | h
        · exact h.symm
        · exfalso
          rcases hb with h' | h'
          · have := congrArg Fin.val h'; simp at this; omega
          · simp at h'; omega
      subst hk'
      refine ⟨z, ?_⟩
      rw [← hzb, glueMap_overlap_chart_succ]
      rfl
    | torus h =>
      refine ⟨torusToOverlap t i z, ?_⟩
      rw [← hzb, glueMap_torus_chart, ← Scheme.Hom.comp_apply, torusToOverlap_overlapToChartRight]
      rfl
  · intro z
    refine ⟨overlapToChartLeft t z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition]

private theorem isPullback_torus (i j : Fin e) (hij : i ≠ j) (h₁ : (j : ℕ) ≠ i + 1) (h₂ :
    (i : ℕ) ≠ j + 1) :
    IsPullback (torusToChart t i) (torusToChart t j) (Resolution.ι t e i) (Resolution.ι t e j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [torusToChart_ι, torusToChart_ι]
  apply preimage_opensRange_eq
  · intro P Q hPQ
    obtain ⟨a, ha, hb, z, hza, hzb⟩ := (ι_apply_eq_iff t e Q P).mp hPQ
    cases a with
    | chart k =>
      simp only [chart_le_chart] at ha hb
      exact absurd (ha.symm.trans hb) hij
    | overlap k hk =>
      simp only [overlap_le_chart] at ha hb
      exfalso
      rcases ha with h | h <;> rcases hb with h' | h'
      · exact hij (h.trans h'.symm)
      · exact h₁ (by rw [h]; exact h')
      · exact h₂ (by rw [h']; exact h)
      · exact hij (Fin.ext (by omega))
    | torus h =>
      exact ⟨z, hzb⟩
  · intro z
    refine ⟨torusToChart t i z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, torusToChart_ι, torusToChart_ι]

private theorem isPullback_self (i : Fin e) :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom))
      (Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom))
      (Resolution.ι t e i) (Resolution.ι t e i) := by
  have : Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom) = 𝟙 (chartScheme t) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id C₀)) = _
    rw [CommRingCat.ofHom_id]
    exact Spec.map_id _
  rw [this]
  exact IsKernelPair.id_of_mono (Resolution.ι t e i)

end squares

section surjective

variable {e}

private theorem eq_mul_invSelf_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : R)
    [IsLocalization.Away x S] (z : S) :
    ∃ (n : ℕ) (a : R), z = algebraMap R S a * IsLocalization.Away.invSelf (S := S) x ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := S) x z
  refine ⟨n, a, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

private theorem surjective_lift_left :
    Function.Surjective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom W C₀ (OverlapRing t)) (transitionUp t)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] OverlapRing t) := by
  intro z
  obtain ⟨n, a, rfl⟩ := eq_mul_invSelf_pow (V t) z
  refine ⟨a ⊗ₜ (U t ^ n), ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, transitionUp_U]
  rfl

private theorem surjective_lift_right :
    Function.Surjective (Algebra.TensorProduct.lift
      (transitionUp t) (IsScalarTower.toAlgHom W C₀ (OverlapRing t))
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] OverlapRing t) := by
  intro z
  obtain ⟨n, a, rfl⟩ := eq_mul_invSelf_pow (V t) z
  refine ⟨(U t ^ n) ⊗ₜ a, ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, transitionUp_U, mul_comm]
  rfl

private theorem surjective_lift_id :
    Function.Surjective (Algebra.TensorProduct.lift (AlgHom.id W C₀) (AlgHom.id W C₀)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] C₀) := by
  intro a
  exact ⟨a ⊗ₜ 1, by rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one]⟩

private theorem algebraMap_mem_of_xT_yT_mem (S : Subalgebra W (TorusRing t)) (hx : xT t ∈ S)
    (hy : yT t ∈ S) (c : C₀) : algebraMap C₀ (TorusRing t) c ∈ S := by
  obtain ⟨p, rfl⟩ := mk_surjective t c
  have key : (IsScalarTower.toAlgHom W C₀ (TorusRing t)).comp (mk t) =
      MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [MvPolynomial.aeval_X]
    fin_cases k <;> rfl
  have h1 : algebraMap C₀ (TorusRing t) (mk t p) =
      MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) p :=
    congrArg (fun φ => φ p) key
  rw [h1]
  have h2 : MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) p ∈
      (MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k)).range :=
    ⟨p, rfl⟩
  rw [← Algebra.adjoin_range_eq_range_aeval] at h2
  refine (Algebra.adjoin_le ?_) h2
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact hx
  · exact hy

private theorem tinv_mem (S : Subalgebra W (TorusRing t)) {a b : ℕ} (hab : a + 2 ≤ b)
    (hx : xT t * tinv t ^ b ∈ S) (hy : yT t * tT t ^ a ∈ S) : tinv t ∈ S := by
  have htT : tT t ∈ S := S.algebraMap_mem t
  have hprod : xT t * tinv t ^ b * (yT t * tT t ^ a) = tinv t ^ (b - a - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, b = a + 1 + m := ⟨b - a - 1, by omega⟩
    rw [show a + 1 + m - a - 1 = m by omega]
    have h1 := xT_mul_yT t
    have h2 := tT_pow_mul_tinv_pow t (a + 1)
    calc xT t * tinv t ^ (a + 1 + m) * (yT t * tT t ^ a)
        = (xT t * yT t) * tT t ^ a * tinv t ^ (a + 1) * tinv t ^ m := by ring
      _ = tinv t ^ m := by rw [h1, ← pow_succ', h2, one_mul]
  have hm : tinv t ^ (b - a - 1) ∈ S := hprod ▸ S.mul_mem hx hy
  have : tinv t = tinv t ^ (b - a - 1) * tT t ^ (b - a - 2) := by
    obtain ⟨m, hm'⟩ : ∃ m, b - a - 1 = m + 1 := ⟨b - a - 2, by omega⟩
    rw [hm', show b - a - 2 = m by omega, pow_succ, mul_assoc, mul_comm (tinv t) (tT t ^ m),
      ← mul_assoc, tinv_pow_mul_tT_pow, one_mul]
  rw [this]
  exact S.mul_mem hm (S.pow_mem htT _)

private theorem surjective_lift_torus (i j : ℕ) (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
    Function.Surjective (Algebra.TensorProduct.lift (torusChart t i) (torusChart t j)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] TorusRing t) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  set S := (Algebra.TensorProduct.lift (torusChart t i) (torusChart t j)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] TorusRing t).range
  have hxi : xT t * tinv t ^ i ∈ S := (AlgHom.mem_range _).mpr ⟨U t ⊗ₜ 1, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, torusChart_U]⟩
  have hyi : yT t * tT t ^ i ∈ S := (AlgHom.mem_range _).mpr ⟨V t ⊗ₜ 1, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, torusChart_V]⟩
  have hxj : xT t * tinv t ^ j ∈ S := (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ U t, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, torusChart_U]⟩
  have hyj : yT t * tT t ^ j ∈ S := (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ V t, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, torusChart_V]⟩
  have htinv : tinv t ∈ S := by
    rcases h with h | h
    · exact tinv_mem t S h hxj hyi
    · exact tinv_mem t S h hxi hyj
  have htT : tT t ∈ S := S.algebraMap_mem t
  have hx : xT t ∈ S := by
    have : xT t = xT t * tinv t ^ i * tT t ^ i := by rw [mul_assoc, tinv_pow_mul_tT_pow, mul_one]
    rw [this]; exact S.mul_mem hxi (S.pow_mem htT _)
  have hy : yT t ∈ S := by
    have : yT t = yT t * tT t ^ i * tinv t ^ i := by rw [mul_assoc, tT_pow_mul_tinv_pow, mul_one]
    rw [this]; exact S.mul_mem hyi (S.pow_mem htinv _)
  intro z _
  obtain ⟨n, c, rfl⟩ := eq_mul_invSelf_pow (S := TorusRing t)
    (algebraMap W (CrossingQuotient W t) t) z
  exact S.mul_mem (algebraMap_mem_of_xT_yT_mem t S hx hy c) (S.pow_mem htinv _)

end surjective

private theorem block (i j : Fin e) :
    IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j)
        (toSpec t e)) := by
  by_cases hij : i = j
  · subst hij
    exact isClosedImmersion_mapDesc t e (AlgHom.id W C₀) (AlgHom.id W C₀) i i
      (isPullback_self i) (surjective_lift_id t)
  by_cases h₁ : (j : ℕ) = i + 1
  · have hi : (i : ℕ) + 1 < e := h₁ ▸ j.2
    obtain rfl : j = ⟨(i : ℕ) + 1, hi⟩ := Fin.ext h₁
    exact isClosedImmersion_mapDesc t e (IsScalarTower.toAlgHom W C₀ (OverlapRing t))
      (transitionUp t) i _ (isPullback_overlap i hi) (surjective_lift_left t)
  by_cases h₂ : (i : ℕ) = j + 1
  · have hj : (j : ℕ) + 1 < e := h₂ ▸ i.2
    obtain rfl : i = ⟨(j : ℕ) + 1, hj⟩ := Fin.ext h₂
    exact isClosedImmersion_mapDesc t e (transitionUp t)
      (IsScalarTower.toAlgHom W C₀ (OverlapRing t)) _ j (isPullback_overlap j hj).flip
      (surjective_lift_right t)
  · have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    exact isClosedImmersion_mapDesc t e (torusChart t i) (torusChart t j) i j
      (isPullback_torus i j hij h₁ h₂) (surjective_lift_torus t i j (by omega))

private theorem isSeparated_toSpec : IsSeparated (toSpec t e) := isSeparated_of_blocks t e
    (block t e)

set_option backward.isDefEq.respectTransparency.types false in
private theorem isSeparated : (Resolution t e).IsSeparated :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := toSpec t e)).mp
      (isSeparated_toSpec t e)

end CrossingResolutionSeparatedAux

/-- The resolution is separated, and so is its morphism to the crossing scheme. -/
theorem MvPolynomial.CrossingQuotient.Resolution.isSeparated
    {W : Type u3} [CommRing W] (t : W) (e : ℕ) :
    (Resolution t e).IsSeparated ∧ IsSeparated (Resolution.toCrossing t e) := by
  have := CrossingResolutionSeparatedAux.isSeparated t e
  exact ⟨this, inferInstance⟩

universe u4

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution morphism is locally of finite type and quasi-compact. -/
theorem MvPolynomial.CrossingQuotient.Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing
    {W : Type u4} [CommRing W] (t : W) (e : ℕ) :
    LocallyOfFiniteType (Resolution.toCrossing t e) ∧ QuasiCompact (Resolution.toCrossing t e) := by
  constructor
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
      (Resolution.openCover t e)]
    intro i
    have hι := Resolution.ι_toCrossing t e (i : Fin e)
    change LocallyOfFiniteType (Resolution.ι t e (i : Fin e) ≫ Resolution.toCrossing t e)
    rw [hι, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change RingHom.FiniteType (resolutionChart t e i).toRingHom
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap W (CrossingQuotient W (t ^ e))) ?_
    have hc : (resolutionChart t e i).toRingHom.comp (algebraMap W (CrossingQuotient W (t ^ e))) =
        algebraMap W (CrossingQuotient W t) := RingHom.ext fun w =>
            (resolutionChart t e i).commutes w
    rw [hc, RingHom.finiteType_algebraMap]
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ W _)
        (Ideal.Quotient.mkₐ_surjective W _)
  · have hc : CompactSpace (chartScheme t) := by
      have h := (isAffineOpen_top (chartScheme t)).isCompact
      exact isCompact_univ_iff.mp (by simpa using h)
    have : CompactSpace (Resolution t e) := by
      constructor
      have h : (Set.univ : Set (Resolution t e)) = ⋃ i : Fin e,
          Set.range (Resolution.ι t e i).base := by
        ext x
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq t e x
        exact ⟨i, y, rfl⟩
      rw [h]
      exact isCompact_iUnion fun i => isCompact_range (Resolution.ι t e i).continuous
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr
      ‹CompactSpace (Resolution t e)›

universe u5

/-- The resolution morphism of the crossing `X * Y = t ^ e` is proper. -/
theorem MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing
    {W : Type u5} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) := by
  obtain ⟨-, hsep⟩ := Resolution.isSeparated t e
  obtain ⟨hft, hqc⟩ := Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing t e
  have huc : UniversallyClosed (Resolution.toCrossing t e) :=
    UniversallyClosed.of_valuativeCriterion _
      (Resolution.valuativeCriterion_existence_toCrossing t e)
  exact IsProper.mk
