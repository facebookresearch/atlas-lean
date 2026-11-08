/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Algebra.Algebra.FrobeniusDivisionWanted

/-!
# Frobenius theorem on real division algebras

Proves the classification of finite-dimensional associative division ℝ-algebras.
-/

-- Helper 1: the structure map ℝ → A is injective (ℝ is a field, A nontrivial).
private lemma algMap_injective {A : Type*} [DivisionRing A] [Algebra ℝ A] :
    Function.Injective (algebraMap ℝ A) :=
  RingHom.injective (algebraMap ℝ A)

-- Helper 2: every element is integral over ℝ (finite-dimensionality).
private lemma isIntegral_mem {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (x : A) : IsIntegral ℝ x := by
  have h : Algebra.IsIntegral ℝ A := Algebra.IsIntegral.of_finite ℝ A
  exact h.isIntegral x

-- Helper 3: every element satisfies a real polynomial of degree ≤ 2.
private lemma minpoly_natDegree_le_two {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (x : A) : (minpoly ℝ x).natDegree ≤ 2 := by
  have hirr : Irreducible (minpoly ℝ x) :=
    minpoly.irreducible (isIntegral_mem x)
  have hdeg : (minpoly ℝ x).degree ≤ 2 := Irreducible.degree_le_two hirr
  exact Polynomial.natDegree_le_of_degree_le hdeg

-- Helper 4 (degree analysis): a nonreal element has quadratic minpoly, giving
-- an explicit relation `x ^ 2 + c₁ • x + c₀ = 0`.
private lemma quad_relation {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {x : A} (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
    ∃ c₁ c₀ : ℝ, x ^ 2 + algebraMap ℝ A c₁ * x + algebraMap ℝ A c₀ = 0 := by
  have hint : IsIntegral ℝ x := isIntegral_mem x
  have hmonic : (minpoly ℝ x).Monic := minpoly.monic hint
  have hdeg2 : (minpoly ℝ x).natDegree ≤ 2 := minpoly_natDegree_le_two x
  have haeval : Polynomial.aeval x (minpoly ℝ x) = 0 := minpoly.aeval ℝ x
  have hdeg0 : (minpoly ℝ x).natDegree ≠ 0 := by
    intro h0
    have hform : minpoly ℝ x = Polynomial.C ((minpoly ℝ x).coeff 0) := by
      ext n
      simp only [Polynomial.coeff_C]
      by_cases hn : n = 0
      · subst hn; rfl
      · rw [ite_eq_right hn]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hc1 : (minpoly ℝ x).coeff 0 = 1 := by
      have hmc := hmonic.coeff_natDegree
      rw [h0] at hmc
      exact hmc
    rw [hform, Polynomial.aeval_C] at haeval
    have hcz : (minpoly ℝ x).coeff 0 = 0 :=
      algMap_injective (by rw [haeval, map_zero])
    rw [hc1] at hcz
    exact one_ne_zero hcz
  have hdeg1 : (minpoly ℝ x).natDegree ≠ 1 := by
    intro h1
    have hform : minpoly ℝ x
        = Polynomial.X + Polynomial.C ((minpoly ℝ x).coeff 0) := by
      ext n
      rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      by_cases hn0 : n = 0
      · subst hn0
        simp
      · by_cases hn1 : n = 1
        · subst hn1
          have hmc := hmonic.coeff_natDegree
          rw [h1] at hmc
          simp [hmc]
        · have h0 : (minpoly ℝ x).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have e1 : (1 : ℕ) ≠ n := fun h => hn1 h.symm
          simp [h0, hn0, e1]
    rw [hform] at haeval
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haeval
    have h2 : x = -(algebraMap ℝ A ((minpoly ℝ x).coeff 0)) :=
      eq_neg_of_add_eq_zero_left haeval
    have hxmem : x = algebraMap ℝ A (-((minpoly ℝ x).coeff 0)) := by
      rw [map_neg]
      exact h2
    exact hx _ hxmem.symm
  have hdeg : (minpoly ℝ x).natDegree = 2 := by omega
  have hform : minpoly ℝ x = Polynomial.X ^ 2
      + Polynomial.C ((minpoly ℝ x).coeff 1) * Polynomial.X
      + Polynomial.C ((minpoly ℝ x).coeff 0) := by
    ext n
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · by_cases hn1 : n = 1
      · subst hn1
        have hmc := hmonic.coeff_natDegree
        rw [hdeg] at hmc
        simp
      · by_cases hn2 : n = 2
        · subst hn2
          have hmc := hmonic.coeff_natDegree
          rw [hdeg] at hmc
          simp [hmc]
        · have h0 : (minpoly ℝ x).coeff n = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have e1 : (1 : ℕ) ≠ n := fun h => hn1 h.symm
          simp [h0, hn0, e1, hn2]
  rw [hform] at haeval
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at haeval
  exact ⟨_, _, haeval⟩

-- Helper 5 (complete the square): a nonreal element yields `u` with `u * u = -1`.
private lemma exists_sq_eq_neg_one {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {x : A} (hx : ∀ r : ℝ, algebraMap ℝ A r ≠ x) :
    ∃ u : A, u * u = -1 := by
  obtain ⟨c₁, c₀, hquad⟩ := quad_relation hx
  have hcentral : ∀ y : ℝ, algebraMap ℝ A y * x = x * algebraMap ℝ A y :=
    fun y => (Algebra.commute_algebraMap_left y x).eq
  have hxx : x ^ 2
      = -(algebraMap ℝ A c₁ * x) - algebraMap ℝ A c₀ := by
    have h2 : x ^ 2 + (algebraMap ℝ A c₁ * x + algebraMap ℝ A c₀) = 0 := by
      rw [← add_assoc]
      exact hquad
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [neg_add] at h3
    rw [sub_eq_add_neg]
    exact h3
  have hm1 : algebraMap ℝ A c₁ * x
      = algebraMap ℝ A (c₁ / 2) * x + algebraMap ℝ A (c₁ / 2) * x := by
    have hc : algebraMap ℝ A c₁
        = algebraMap ℝ A (c₁ / 2) + algebraMap ℝ A (c₁ / 2) := by
      have hc2 : c₁ = c₁ / 2 + c₁ / 2 := by ring
      conv_lhs => rw [hc2]
      rw [map_add]
    rw [hc, add_mul]
  have hmm : algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2)
      = algebraMap ℝ A ((c₁ / 2) ^ 2) := by
    rw [← map_mul, pow_two]
  set t : A := x + algebraMap ℝ A (c₁ / 2) with ht
  have hexpand : t * t = x ^ 2
      + (algebraMap ℝ A (c₁ / 2) * x + algebraMap ℝ A (c₁ / 2) * x)
      + algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2) := by
    have e1 : (x + algebraMap ℝ A (c₁ / 2)) * (x + algebraMap ℝ A (c₁ / 2))
        = x * x + x * algebraMap ℝ A (c₁ / 2)
          + (algebraMap ℝ A (c₁ / 2) * x
            + algebraMap ℝ A (c₁ / 2) * algebraMap ℝ A (c₁ / 2)) := by
      rw [add_mul, mul_add, mul_add]
    have e2 : x * algebraMap ℝ A (c₁ / 2)
        = algebraMap ℝ A (c₁ / 2) * x := (hcentral (c₁ / 2)).symm
    rw [ht, e1, e2, ← pow_two]
    abel
  have htsq : t * t = algebraMap ℝ A ((c₁ / 2) ^ 2 - c₀) := by
    rw [hexpand, hxx, hm1, hmm, map_sub]
    abel
  by_cases hge : 0 ≤ (c₁ / 2) ^ 2 - c₀
  · -- Nonnegative case: `t` is (plus/minus) a real, contradicting `hx`.
    set s := Real.sqrt ((c₁ / 2) ^ 2 - c₀) with hs
    have hss : s * s = (c₁ / 2) ^ 2 - c₀ := Real.mul_self_sqrt hge
    have hts : t * t
        = algebraMap ℝ A s * algebraMap ℝ A s := by
      rw [htsq, ← hss, ← map_mul]
    have hfac : (t - algebraMap ℝ A s) * (t + algebraMap ℝ A s) = 0 := by
      have hcen : algebraMap ℝ A s * t = t * algebraMap ℝ A s :=
        (Algebra.commute_algebraMap_left s t).eq
      have hexp : (t - algebraMap ℝ A s) * (t + algebraMap ℝ A s)
          = (t * t + t * algebraMap ℝ A s)
            - (algebraMap ℝ A s * t
              + algebraMap ℝ A s * algebraMap ℝ A s) := by
        noncomm_ring
      rw [hexp, hcen, hts]
      abel
    rcases mul_eq_zero.mp hfac with h | h
    · have htS : t = algebraMap ℝ A s := sub_eq_zero.mp h
      have hsub : x = t - algebraMap ℝ A (c₁ / 2) := by
        rw [ht]
        abel
      have hxeq : x = algebraMap ℝ A (s - c₁ / 2) := by
        rw [hsub, htS, ← map_sub]
      exact (hx _ hxeq.symm).elim
    · have htS : t = -(algebraMap ℝ A s) := eq_neg_of_add_eq_zero_left h
      have hsub : x = t - algebraMap ℝ A (c₁ / 2) := by
        rw [ht]
        abel
      have hxeq : x = algebraMap ℝ A (-s - c₁ / 2) := by
        rw [hsub, htS, map_sub, map_neg]
      exact (hx _ hxeq.symm).elim
  · -- Negative case: normalize `t` to a square root of `-1`.
    push Not at hge
    have hpos : 0 < -((c₁ / 2) ^ 2 - c₀) := neg_pos.mpr hge
    set d := Real.sqrt (-((c₁ / 2) ^ 2 - c₀)) with hd
    have hdd : d * d = -((c₁ / 2) ^ 2 - c₀) :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have hd0 : d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hSd0 : algebraMap ℝ A d ≠ 0 := by
      intro hz
      have hz' : algebraMap ℝ A d = algebraMap ℝ A 0 := by
        rw [hz, map_zero]
      exact hd0 (algMap_injective hz')
    have hcommd : algebraMap ℝ A d * t = t * algebraMap ℝ A d :=
      (Algebra.commute_algebraMap_left d t).eq
    have hinvcomm : (algebraMap ℝ A d)⁻¹ * t
        = t * (algebraMap ℝ A d)⁻¹ := by
      apply mul_left_cancel₀ hSd0
      rw [← mul_assoc (algebraMap ℝ A d) _ _,
        mul_inv_cancel₀ hSd0, one_mul,
        ← mul_assoc (algebraMap ℝ A d) t _,
        hcommd, mul_assoc t _ _,
        mul_inv_cancel₀ hSd0, mul_one]
    refine ⟨t * (algebraMap ℝ A d)⁻¹, ?_⟩
    set w : A := (algebraMap ℝ A d)⁻¹ with hw
    have hmove : t * w * (t * w) = (t * t) * (w * w) := by
      rw [mul_assoc t w (t * w), ← mul_assoc w t w, hinvcomm,
        mul_assoc t w w, ← mul_assoc t t (w * w)]
    have hww : w * w = algebraMap ℝ A ((d * d)⁻¹) := by
      rw [hw, ← mul_inv_rev, ← map_mul, ← map_inv₀]
    have hed : ((c₁ / 2) ^ 2 - c₀) * ((d * d)⁻¹) = -1 := by
      have hene : (c₁ / 2) ^ 2 - c₀ ≠ 0 := ne_of_lt hge
      rw [hdd, inv_neg, mul_neg, mul_inv_cancel₀ hene]
    rw [hmove, htsq, hww, ← map_mul, hed, map_neg, map_one]

-- Helper 6: the complex embedding from a square root of `-1`, and its injectivity.
private noncomputable def complexHom {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {u : A} (hu : u * u = -1) : ℂ →ₐ[ℝ] A :=
  Complex.lift ⟨u, hu⟩

private lemma complexHom_injective {A : Type*} [DivisionRing A] [Algebra ℝ A]
    (f : ℂ →ₐ[ℝ] A) : Function.Injective f :=
  RingHom.injective f.toRingHom

-- Helper 7: a linear injection between spaces of equal finite rank is surjective.
private lemma surjective_of_injective_of_finrank_eq {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (g : E →ₗ[ℝ] F) (hinj : Function.Injective g)
    (h : Module.finrank ℝ E = Module.finrank ℝ F) :
    Function.Surjective g := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hker : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hfr := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, finrank_bot, add_zero] at hfr
  rw [hfr, h]

-- Helper 8: the dimension-one case is `ℝ` itself.
private lemma equiv_real_of_finrank_one {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (h : Module.finrank ℝ A = 1) :
    Nonempty (A ≃ₐ[ℝ] ℝ) := by
  have hbij : Function.Bijective (Algebra.ofId ℝ A) := by
    refine ⟨algMap_injective, ?_⟩
    have hs := surjective_of_injective_of_finrank_eq
      (Algebra.ofId ℝ A).toLinearMap algMap_injective
      (by rw [Module.finrank_self, h])
    exact hs
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId ℝ A) hbij).symm⟩

-- Helper 9: the dimension-two case is `ℂ`.
private lemma equiv_complex_of_finrank_two {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (f : ℂ →ₐ[ℝ] A) (hf : Function.Injective f)
    (h : Module.finrank ℝ A = 2) : Nonempty (A ≃ₐ[ℝ] ℂ) := by
  have hbij : Function.Bijective f := by
    refine ⟨hf, ?_⟩
    have hs := surjective_of_injective_of_finrank_eq f.toLinearMap hf
      (by rw [Complex.finrank_real_complex, h])
    exact hs
  exact ⟨(AlgEquiv.ofBijective f hbij).symm⟩

-- Helper 10: with a copy of `ℂ` inside, the real dimension is even.
private lemma finrank_complex_tower {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (f : ℂ →ₐ[ℝ] A) :
    ∃ m : ℕ, Module.finrank ℝ A = 2 * m := by
  -- Name the structures explicitly: the `ℂ`-action via `f`, and the original
  -- `ℝ`-action (so restriction of scalars along `ℝ → ℂ` cannot shadow it).
  let cmod : Module ℂ A := Module.compHom A f.toRingHom
  let orig : Module ℝ A := Algebra.toModule
  have hst : IsScalarTower ℝ ℂ A := ⟨fun r c a => by
    change f (r • c) * a = r • (f c * a)
    rw [Algebra.smul_def r c, map_mul, AlgHom.commutes f r,
      Algebra.smul_def r (f c * a), mul_assoc]
  ⟩
  have := Module.Free.of_divisionRing ℂ A
  have htower :=
    @Module.finrank_mul_finrank ℝ ℂ A _ _ _ _ cmod orig hst _ _ _ _
  rw [Complex.finrank_real_complex] at htower
  exact ⟨_, htower.symm⟩

-- Helper 11: a finite-dimensional real field is `ℝ` or `ℂ` (dimension 1 or 2).
private lemma field_finrank {K : Type*} [Field K] [Algebra ℝ K]
    [FiniteDimensional ℝ K] :
    Module.finrank ℝ K = 1 ∨ Module.finrank ℝ K = 2 := by
  by_cases hK : ∀ z : K, ∃ r : ℝ, algebraMap ℝ K r = z
  · left
    have hbij : Function.Bijective (Algebra.ofId ℝ K) := by
      refine ⟨algMap_injective, ?_⟩
      intro z
      exact hK z
    have e := AlgEquiv.ofBijective (Algebra.ofId ℝ K) hbij
    have hfin := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_self] at hfin
    exact hfin.symm
  · right
    rw [not_forall] at hK
    obtain ⟨z, hz⟩ := hK
    obtain ⟨u, hu⟩ :=
      exists_sq_eq_neg_one (fun r hr => hz ⟨r, hr⟩)
    set f : ℂ →ₐ[ℝ] K := complexHom hu with hf
    have hfinj : Function.Injective f := complexHom_injective f
    obtain ⟨m, hm⟩ := finrank_complex_tower f
    have hm1 : m = 1 := by
      have hsurj : Function.Surjective f := by
        intro α
        by_contra hne
        have hαne : ∀ r : ℝ, algebraMap ℝ K r ≠ α := by
          intro r hr
          apply hne
          exact ⟨algebraMap ℝ ℂ r, by rw [AlgHom.commutes f r]; exact hr⟩
        obtain ⟨c₁, c₀, hquad⟩ := quad_relation hαne
        -- A square root in `ℂ` of the discriminant remainder, via FTA.
        have hnat : (Polynomial.X ^ 2
            - Polynomial.C (algebraMap ℝ ℂ ((c₁ / 2) ^ 2 - c₀)) :
            Polynomial ℂ).natDegree = 2 := by
          compute_degree
          exact one_ne_zero
        have hne2 : (Polynomial.X ^ 2
            - Polynomial.C (algebraMap ℝ ℂ ((c₁ / 2) ^ 2 - c₀)) :
            Polynomial ℂ) ≠ 0 := by
          intro hcon
          have hcc := congrArg Polynomial.natDegree hcon
          rw [hnat, Polynomial.natDegree_zero] at hcc
          norm_num at hcc
        have hdeg2 : 0 < (Polynomial.X ^ 2
            - Polynomial.C (algebraMap ℝ ℂ ((c₁ / 2) ^ 2 - c₀)) :
            Polynomial ℂ).degree := by
          rw [Polynomial.degree_eq_natDegree hne2, hnat]
          decide
        obtain ⟨s, hs⟩ := Complex.exists_root hdeg2
        have hss : s ^ 2 = algebraMap ℝ ℂ ((c₁ / 2) ^ 2 - c₀) := by
          have h0 : (Polynomial.X ^ 2
              - Polynomial.C (algebraMap ℝ ℂ ((c₁ / 2) ^ 2 - c₀))).eval
              s = 0 := hs
          simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C] at h0
          exact sub_eq_zero.mp h0
        -- The quadratic splits over `ℂ`.
        set l₁ : ℂ := -(algebraMap ℝ ℂ (c₁ / 2)) + s with hl₁
        set l₂ : ℂ := -(algebraMap ℝ ℂ (c₁ / 2)) - s with hl₂
        have hsum : l₁ + l₂ = -(algebraMap ℝ ℂ c₁) := by
          have hc2 : algebraMap ℝ ℂ c₁
              = algebraMap ℝ ℂ (c₁ / 2) + algebraMap ℝ ℂ (c₁ / 2) := by
            have hc2' : c₁ = c₁ / 2 + c₁ / 2 := by ring
            conv_lhs => rw [hc2']
            rw [map_add]
          rw [hl₁, hl₂, hc2]
          ring
        have hprod : l₁ * l₂ = algebraMap ℝ ℂ c₀ := by
          have e1 : l₁ * l₂
              = algebraMap ℝ ℂ ((c₁ / 2) ^ 2) - s ^ 2 := by
            rw [hl₁, hl₂, map_pow]
            ring
          rw [e1, hss, map_sub]
          abel
        -- Transport the factorization to `K` and conclude.
        have e1 : f l₁ + f l₂ = -(algebraMap ℝ K c₁) := by
          rw [← map_add, hsum, map_neg, AlgHom.commutes]
        have e2 : f l₁ * f l₂ = algebraMap ℝ K c₀ := by
          rw [← map_mul, hprod, AlgHom.commutes]
        have hfactor0 : (α - f l₁) * (α - f l₂) = 0 := by
          have hfac : (α - f l₁) * (α - f l₂)
              = (α ^ 2 + algebraMap ℝ K c₁ * α + algebraMap ℝ K c₀)
                - ((f l₁ + f l₂ + algebraMap ℝ K c₁) * α)
                + (f l₁ * f l₂ - algebraMap ℝ K c₀) := by
            ring
          rw [hfac, e1, e2, hquad]
          simp
        rcases mul_eq_zero.mp hfactor0 with h | h
        · exact hne ⟨l₁, (sub_eq_zero.mp h).symm⟩
        · exact hne ⟨l₂, (sub_eq_zero.mp h).symm⟩
      have hbij : Function.Bijective f := ⟨hfinj, hsurj⟩
      have e := AlgEquiv.ofBijective f hbij
      have hfin := e.toLinearEquiv.finrank_eq
      rw [Complex.finrank_real_complex] at hfin
      omega
    omega

-- Helper 12: expand `complexHom` on `z = re + im * I`.
private lemma complexHom_apply {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {u : A} (hu : u * u = -1) (z : ℂ) :
    complexHom hu z = algebraMap ℝ A z.re + z.im • u := by
  change (Complex.lift ⟨u, hu⟩) z = _
  rw [Complex.lift_apply, Complex.liftAux_apply]

-- Helper 13: the adjoin of two commuting elements is commutative.
private lemma adjoin_pair_comm {A : Type*} [Ring A] [Algebra ℝ A] {i y : A}
    (h : Commute i y) : ∀ x ∈ Algebra.adjoin ℝ ({i, y} : Set A),
    ∀ z ∈ Algebra.adjoin ℝ ({i, y} : Set A), Commute x z := by
  intro x hx
  refine Algebra.adjoin_induction
    (p := fun x _ => ∀ z ∈ Algebra.adjoin ℝ ({i, y} : Set A), Commute x z)
    ?_ ?_ ?_ ?_ hx
  · intro g hg z hz
    refine Algebra.adjoin_induction (p := fun z _ => Commute g z) ?_ ?_ ?_ ?_ hz
    · intro h2 hh2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh2
      rcases hg with rfl | rfl <;> rcases hh2 with rfl | rfl
      · exact Commute.refl _
      · exact h
      · exact h.symm
      · exact Commute.refl _
    · intro r
      exact (Algebra.commute_algebraMap_left r g).symm
    · intro a b _ _ iha ihb
      exact iha.add_right ihb
    · intro a b _ _ iha ihb
      exact iha.mul_right ihb
  · intro r z hz
    exact Algebra.commute_algebraMap_left r z
  · intro a b _ _ iha ihb z hz
    exact (iha z hz).add_left (ihb z hz)
  · intro a b _ _ iha ihb z hz
    exact (iha z hz).mul_left (ihb z hz)

-- Helper 14: the centralizer of `i` is the range of `complexHom`.
private lemma centralizer_eq_range {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {i : A} (hi : i * i = -1) (y : A)
    (hy : y * i = i * y) : y ∈ AlgHom.range (complexHom hi) := by
  set T : Subalgebra ℝ A := Algebra.adjoin ℝ ({i, y} : Set A) with hT
  let : Algebra ℝ T := T.algebra
  let : Module ℝ T := Algebra.toModule
  let : FiniteDimensional ℝ T := FiniteDimensional.finiteDimensional_subalgebra T
  have hiT : i ∈ T :=
    Algebra.subset_adjoin (Set.mem_insert i {y})
  have hcommT : ∀ x ∈ T, ∀ z ∈ T, Commute x z :=
    fun x hx z hz => adjoin_pair_comm hy.symm x hx z hz
  -- `T` is a field: commutative by `hcommT`, inverses by finite-dimensionality.
  have hfield : IsField ↥T := by
    refine IsField.mk ?_ ?_ ?_
    · exact exists_pair_ne _
    · intro x y
      apply Subtype.ext
      simpa using (hcommT _ x.2 _ y.2).eq
    · intro a ha
      let hL : ↥T →ₗ[ℝ] ↥T :=
        { toFun := fun x => a * x
          map_add' := fun x y => mul_add _ _ _
          map_smul' := fun r x => Algebra.mul_smul_comm _ _ _ }
      have hinj : Function.Injective hL := by
        intro x y hxy
        have hxy' : a * x = a * y := hxy
        have hsub : a * (x - y) = 0 := by rw [mul_sub, hxy', sub_self]
        have hsubA : (a : A) * ((x : A) - (y : A)) = 0 := by
          have hcc := congrArg Subtype.val hsub
          simpa using hcc
        rcases mul_eq_zero.mp hsubA with h | h
        · exact absurd h (fun h0 => ha (Subtype.ext h0))
        · have hxy0 : x - y = 0 := Subtype.ext h
          exact sub_eq_zero.mp hxy0
      have hsurj := LinearMap.surjective_of_injective hinj
      obtain ⟨b, hb⟩ := hsurj 1
      exact ⟨b, hb⟩
  let : Field ↥T := IsField.toField hfield
  -- `T` has dimension 2: dimension 1 would make `i` real.
  have hT2 : Module.finrank ℝ ↥T = 2 := by
    have hT12 := field_finrank (K := ↥T)
    rcases hT12 with h1 | h2
    · exfalso
      obtain ⟨e⟩ := equiv_real_of_finrank_one h1
      have hr2 : e ⟨i, hiT⟩ * e ⟨i, hiT⟩ = -1 := by
        have h1 : (⟨i, hiT⟩ * ⟨i, hiT⟩ : ↥T) = -1 := by
          apply Subtype.ext
          simpa using hi
        rw [← map_mul, h1, map_neg, map_one]
      have hnn := mul_self_nonneg (e ⟨i, hiT⟩)
      rw [hr2] at hnn
      norm_num at hnn
    · exact h2
  -- The range of `complexHom` sits inside `T` and also has dimension 2.
  have hST : ∀ z : ℂ, complexHom hi z ∈ T := by
    intro z
    rw [complexHom_apply hi z, Algebra.smul_def]
    exact add_mem (Subalgebra.algebraMap_mem _ _)
      (mul_mem (Subalgebra.algebraMap_mem _ _) hiT)
  have hS2 : Module.finrank ℝ ↥(AlgHom.range (complexHom hi)) = 2 := by
    have e := AlgEquiv.ofInjective (complexHom hi) (complexHom_injective _)
    have hfin := e.toLinearEquiv.finrank_eq
    rw [Complex.finrank_real_complex] at hfin
    exact hfin.symm
  -- Hence the two submodules coincide, and `y ∈ T` lands in the range.
  have hle : (AlgHom.range (complexHom hi)).toSubmodule ≤ T.toSubmodule := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule] at hx ⊢
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp hx
    rw [← hz]
    exact hST z
  have hfin_eq : Module.finrank ℝ ↥(AlgHom.range (complexHom hi)).toSubmodule
      = Module.finrank ℝ ↥T.toSubmodule := by
    have e1 : Module.finrank ℝ ↥(AlgHom.range (complexHom hi)).toSubmodule
        = 2 := hS2
    have e2 : Module.finrank ℝ ↥T.toSubmodule = 2 := hT2
    rw [e1, e2]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin_eq
  have hyT : y ∈ T.toSubmodule :=
    (Subalgebra.mem_toSubmodule _).mpr
      (Algebra.subset_adjoin (by simp : y ∈ ({i, y} : Set A)))
  rw [← heq] at hyT
  exact (Subalgebra.mem_toSubmodule _).mp hyT

-- Helper 15: `(2 : A)` is nonzero.
private lemma two_ne_zero {A : Type*} [DivisionRing A] [Algebra ℝ A] : (2 : A) ≠ 0 := by
  have h22 : (2 : A) = algebraMap ℝ A 2 := by
    rw [show (2 : ℝ) = 1 + 1 from one_add_one_eq_two.symm,
      show (2 : A) = 1 + 1 from one_add_one_eq_two.symm,
      map_add, RingHom.map_one]
  intro hcon
  have h2r : (2 : ℝ) ≠ 0 := by norm_num
  apply h2r
  have hcon2 : algebraMap ℝ A 2 = algebraMap ℝ A 0 := by
    rw [← h22, hcon, map_zero]
  exact algMap_injective hcon2

-- Helper 16: `X + X = 0` forces `X = 0` (characteristic zero).
private lemma eq_zero_of_add_self {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {X : A} (h : X + X = 0) : X = 0 := by
  have h2Y : (2 : A) * X = 0 := by
    have hcc : (2 : A) * X = X + X := two_mul X
    rw [hcc]; exact h
  rcases mul_eq_zero.mp h2Y with h2ne | h0
  · exact absurd h2ne two_ne_zero
  · exact h0

-- Helper 17: outside the complex subalgebra sits an anticommuting square root of `-1`.
private lemma exists_anticommute {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] {i : A} (hi : i * i = -1)
    {w : A} (hw : w ∉ AlgHom.range (complexHom hi)) :
    ∃ j : A, j * j = -1 ∧ i * j + j * i = 0 := by
  have hi_ne : i ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hi
    have h01 : (0 : A) = 1 := by simpa using congrArg Neg.neg hi
    exact one_ne_zero h01.symm
  set j₀ : A := i * w - w * i with hj₀def
  have hj₀_ne : j₀ ≠ 0 := by
    intro h0
    apply hw
    have hcomm : w * i = i * w := by
      have h := sub_eq_zero.mp (hj₀def ▸ h0)
      exact h.symm
    exact centralizer_eq_range hi w hcomm
  have hanti : i * j₀ + j₀ * i = 0 := by
    have e : i * j₀ + j₀ * i = (i * i) * w - w * (i * i) := by
      rw [hj₀def]
      noncomm_ring
    rw [e, hi]
    simp
  have hanti' : i * j₀ = -(j₀ * i) := eq_neg_of_add_eq_zero_left hanti
  have hsq_comm : (j₀ * j₀) * i = i * (j₀ * j₀) := by
    have e1 : i * (j₀ * j₀) = (i * j₀) * j₀ := (mul_assoc _ _ _).symm
    have e2 : (j₀ * j₀) * i = j₀ * (j₀ * i) := mul_assoc _ _ _
    rw [e1, e2, hanti', neg_mul, mul_assoc, hanti', mul_neg, neg_neg]
  have hmem : j₀ * j₀ ∈ AlgHom.range (complexHom hi) :=
    centralizer_eq_range hi _ hsq_comm
  obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp hmem
  have hexpand : j₀ * j₀ = algebraMap ℝ A z.re + z.im • i := by
    rw [← hz]
    exact complexHom_apply hi z
  -- The imaginary part vanishes: `j₀ * j₀` is real.
  have him0 : z.im = 0 := by
    have hLHS : j₀ * (algebraMap ℝ A z.re + z.im • i)
        = algebraMap ℝ A z.re * j₀ + algebraMap ℝ A z.im * (j₀ * i) := by
      rw [mul_add, Algebra.smul_def, ← mul_assoc j₀ _ _,
        ← (Algebra.commute_algebraMap_left z.im j₀).eq, mul_assoc,
        ← (Algebra.commute_algebraMap_left z.re j₀).eq]
    have hRHS : (algebraMap ℝ A z.re + z.im • i) * j₀
        = algebraMap ℝ A z.re * j₀ + algebraMap ℝ A z.im * (i * j₀) := by
      rw [add_mul, Algebra.smul_def, mul_assoc]
    have key : j₀ * (algebraMap ℝ A z.re + z.im • i)
        = (algebraMap ℝ A z.re + z.im • i) * j₀ := by
      have h := (mul_assoc j₀ j₀ j₀).symm
      rw [hexpand] at h
      exact h
    rw [hLHS, hRHS] at key
    have e : algebraMap ℝ A z.im * (i * j₀)
        = -(algebraMap ℝ A z.im * (j₀ * i)) := by
      rw [hanti', mul_neg]
    rw [e] at key
    have hXX : algebraMap ℝ A z.im * (j₀ * i)
        = -(algebraMap ℝ A z.im * (j₀ * i)) := add_left_cancel_iff.mp key
    have hX : algebraMap ℝ A z.im * (j₀ * i)
        + algebraMap ℝ A z.im * (j₀ * i) = 0 := by
      nth_rewrite 2 [hXX]
      exact add_neg_cancel _
    have hX0 : algebraMap ℝ A z.im * (j₀ * i) = 0 := eq_zero_of_add_self hX
    have hji : j₀ * i ≠ 0 := mul_ne_zero hj₀_ne hi_ne
    have halg0 : algebraMap ℝ A z.im = 0 := by
      rcases mul_eq_zero.mp hX0 with h | h
      · exact h
      · exact absurd h hji
    exact algMap_injective (by rw [halg0, map_zero])
  have hreal : j₀ * j₀ = algebraMap ℝ A z.re := by
    rw [hexpand, him0, zero_smul, add_zero]
  by_cases hge : 0 ≤ z.re
  · -- Nonnegative case: `j₀` is (plus/minus) a real, hence central, forcing `j₀ = 0`.
    set s := Real.sqrt z.re with hs
    have hss : s * s = z.re := Real.mul_self_sqrt hge
    have hts : j₀ * j₀ = algebraMap ℝ A s * algebraMap ℝ A s := by
      rw [hreal, ← hss, ← map_mul]
    have hfac : (j₀ - algebraMap ℝ A s) * (j₀ + algebraMap ℝ A s) = 0 := by
      have hcen : algebraMap ℝ A s * j₀ = j₀ * algebraMap ℝ A s :=
        (Algebra.commute_algebraMap_left s j₀).eq
      have hexp : (j₀ - algebraMap ℝ A s) * (j₀ + algebraMap ℝ A s)
          = (j₀ * j₀ + j₀ * algebraMap ℝ A s)
            - (algebraMap ℝ A s * j₀
              + algebraMap ℝ A s * algebraMap ℝ A s) := by
        noncomm_ring
      rw [hexp, hcen, hts]
      abel
    rcases mul_eq_zero.mp hfac with h | h
    · have hjS : j₀ = algebraMap ℝ A s := sub_eq_zero.mp h
      have hcomm : i * j₀ = j₀ * i := by
        rw [hjS]
        exact (Algebra.commute_algebraMap_left s i).eq.symm
      rw [hcomm] at hanti
      have h0 : j₀ * i = 0 := eq_zero_of_add_self hanti
      rcases mul_eq_zero.mp h0 with h00 | h00
      · exact absurd h00 hj₀_ne
      · exact absurd h00 hi_ne
    · have hjS : j₀ = -(algebraMap ℝ A s) := eq_neg_of_add_eq_zero_left h
      have hcomm : i * j₀ = j₀ * i := by
        rw [hjS, mul_neg, neg_mul, (Algebra.commute_algebraMap_left s i).eq]
      rw [hcomm] at hanti
      have h0 : j₀ * i = 0 := eq_zero_of_add_self hanti
      rcases mul_eq_zero.mp h0 with h00 | h00
      · exact absurd h00 hj₀_ne
      · exact absurd h00 hi_ne
  · -- Negative case: normalize `j₀` to a square root of `-1`.
    have hlt : z.re < 0 := not_le.mp hge
    have hpos : 0 < -(z.re) := neg_pos.mpr hlt
    set d := Real.sqrt (-(z.re)) with hd
    have hdd : d * d = -(z.re) := Real.mul_self_sqrt (le_of_lt hpos)
    have hd0 : d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hSd0 : algebraMap ℝ A d ≠ 0 := by
      intro hz
      have hz' : algebraMap ℝ A d = algebraMap ℝ A 0 := by
        rw [hz, map_zero]
      exact hd0 (algMap_injective hz')
    have hinvcomm : (algebraMap ℝ A d)⁻¹ * j₀
        = j₀ * (algebraMap ℝ A d)⁻¹ := by
      apply mul_left_cancel₀ hSd0
      rw [← mul_assoc (algebraMap ℝ A d) _ _,
        mul_inv_cancel₀ hSd0, one_mul,
        ← mul_assoc (algebraMap ℝ A d) j₀ _,
        (Algebra.commute_algebraMap_left d j₀).eq,
        mul_assoc, mul_inv_cancel₀ hSd0, mul_one]
    refine ⟨j₀ * (algebraMap ℝ A d)⁻¹, ?_, ?_⟩
    · have hmove : j₀ * (algebraMap ℝ A d)⁻¹ * (j₀ * (algebraMap ℝ A d)⁻¹)
          = (j₀ * j₀) * ((algebraMap ℝ A d)⁻¹ * (algebraMap ℝ A d)⁻¹) := by
        rw [mul_assoc j₀ (algebraMap ℝ A d)⁻¹ (j₀ * (algebraMap ℝ A d)⁻¹),
          ← mul_assoc (algebraMap ℝ A d)⁻¹ j₀ (algebraMap ℝ A d)⁻¹,
          hinvcomm,
          mul_assoc j₀ (algebraMap ℝ A d)⁻¹ (algebraMap ℝ A d)⁻¹,
          ← mul_assoc j₀ j₀
            ((algebraMap ℝ A d)⁻¹ * (algebraMap ℝ A d)⁻¹)]
      have hww : (algebraMap ℝ A d)⁻¹ * (algebraMap ℝ A d)⁻¹
          = algebraMap ℝ A ((d * d)⁻¹) := by
        rw [← mul_inv_rev, ← map_mul, ← map_inv₀]
      have hed : z.re * ((d * d)⁻¹) = -1 := by
        have hene : z.re ≠ 0 := ne_of_lt hlt
        rw [hdd, inv_neg, mul_neg, mul_inv_cancel₀ hene]
      rw [hmove, hreal, hww, ← map_mul, hed, map_neg, map_one]
    · have hwAlg : (algebraMap ℝ A d)⁻¹ = algebraMap ℝ A d⁻¹ :=
        (map_inv₀ _ _).symm
      have e1 : i * (j₀ * (algebraMap ℝ A d)⁻¹)
          = (i * j₀) * (algebraMap ℝ A d)⁻¹ :=
        (mul_assoc _ _ _).symm
      have e2 : (j₀ * (algebraMap ℝ A d)⁻¹) * i
          = (j₀ * i) * (algebraMap ℝ A d)⁻¹ := by
        rw [hwAlg, mul_assoc, (Algebra.commute_algebraMap_left d⁻¹ i).eq,
          ← mul_assoc]
      have hsum : i * (j₀ * (algebraMap ℝ A d)⁻¹)
          + (j₀ * (algebraMap ℝ A d)⁻¹) * i
          = (i * j₀ + j₀ * i) * (algebraMap ℝ A d)⁻¹ := by
        rw [e1, e2, add_mul]
      rw [hsum, hanti, zero_mul]

-- Helper 18: quaternion basis data from `i`, `j`
-- (`Quaternion ℝ = QuaternionAlgebra ℝ (-1) 0 (-1)`).
private noncomputable def quatBasis {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    QuaternionAlgebra.Basis (R := ℝ) A (-1) 0 (-1) := by
  refine QuaternionAlgebra.Basis.mk i j (i * j) ?_ ?_ rfl ?_
  · rw [hi, neg_smul, one_smul, zero_smul, add_zero]
  · rw [hj, neg_smul, one_smul]
  · rw [zero_smul, zero_sub]
    exact eq_neg_of_add_eq_zero_right hanti

-- Helper 19: the quaternion embedding and its injectivity.
private noncomputable def quatHom {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) : Quaternion ℝ →ₐ[ℝ] A :=
  (quatBasis hi hj hanti).liftHom

private lemma quatHom_injective {A : Type*} [DivisionRing A] [Algebra ℝ A]
    (f : Quaternion ℝ →ₐ[ℝ] A) : Function.Injective f :=
  RingHom.injective f.toRingHom

-- Helper 20: expansion of `quatHom` on components.
private lemma quatHom_mk {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) (a b c d : ℝ) :
    quatHom hi hj hanti (QuaternionAlgebra.mk a b c d)
      = algebraMap ℝ A a + b • i + c • j + d • (i * j) := by
  change ((quatBasis hi hj hanti).liftHom) _ = _
  rw [QuaternionAlgebra.Basis.liftHom_apply]
  rfl

-- Helper 21: product of two anticommuting elements commutes.
private lemma comm_of_anticomm_anticomm {A : Type*} [DivisionRing A]
    {i j a : A} (ha : i * a = -(a * i)) (hji : j * i = -(i * j)) :
    (a * j) * i = i * (a * j) := by
  have e1 : (a * j) * i = -(a * (i * j)) := by
    rw [mul_assoc, hji, mul_neg]
  have e2 : i * (a * j) = -(a * (i * j)) := by
    rw [← mul_assoc, ha, neg_mul, ← mul_assoc]
  rw [e1, e2]

-- Helper 22: a non-`ℝ` element exists unless the dimension is one.
private lemma exists_nonreal {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A] (h1 : Module.finrank ℝ A ≠ 1) :
    ∃ x : A, ∀ r : ℝ, algebraMap ℝ A r ≠ x := by
  by_contra hcon
  have hall : ∀ z : A, ∃ r : ℝ, algebraMap ℝ A r = z := by
    intro z
    by_contra hz
    apply hcon
    exact ⟨z, fun r hr => hz ⟨r, hr⟩⟩
  have hbij : Function.Bijective (Algebra.ofId ℝ A) := by
    refine ⟨algMap_injective, ?_⟩
    intro z
    exact hall z
  have e := AlgEquiv.ofBijective (Algebra.ofId ℝ A) hbij
  have hfin := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_self] at hfin
  exact h1 hfin.symm

-- Helper 23: the quaternion embedding is surjective. Every `x` decomposes as
-- `u + w * j` with `u`, `w` commuting with `i` (symmetric/antisymmetric parts
-- under conjugation `x ↦ i * x * i`, halved by the central scalar `(2:ℝ)⁻¹`).
private lemma quatHom_surjective {A : Type*} [DivisionRing A] [Algebra ℝ A]
    [FiniteDimensional ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    Function.Surjective (quatHom hi hj hanti) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hji : j * i = -(i * j) := eq_neg_of_add_eq_zero_right hanti
  intro x
  have h1 : (i * x * i) * i = -(i * x) := by
    rw [mul_assoc (i * x) i i, hi, mul_neg, mul_one]
  have h2' : i * (i * x * i) = -(x * i) := by
    rw [← mul_assoc i (i * x) i, ← mul_assoc i i x, hi, neg_mul, one_mul,
      neg_mul]
  have key : (x - i * x * i) * i = i * (x - i * x * i) := by
    rw [sub_mul, mul_sub, h1, h2', sub_neg_eq_add, sub_neg_eq_add]
    exact add_comm _ _
  have key2 : i * (x + i * x * i) = -((x + i * x * i) * i) := by
    rw [add_mul, mul_add, h2', h1, neg_add, neg_neg]
    exact add_comm _ _
  have hu : ((2 : ℝ)⁻¹ • (x - i * x * i)) * i
      = i * ((2 : ℝ)⁻¹ • (x - i * x * i)) := by
    rw [Algebra.smul_def,
      mul_assoc (algebraMap ℝ A ((2 : ℝ)⁻¹)) (x - i * x * i) i,
      ← mul_assoc i _ _,
      ← (Algebra.commute_algebraMap_left ((2 : ℝ)⁻¹) i).eq,
      mul_assoc (algebraMap ℝ A ((2 : ℝ)⁻¹)) i (x - i * x * i), key]
  obtain ⟨z₁, hz₁⟩ := (AlgHom.mem_range _).mp
    (centralizer_eq_range hi _ hu)
  have ha : i * ((2 : ℝ)⁻¹ • (x + i * x * i))
      = -(((2 : ℝ)⁻¹ • (x + i * x * i)) * i) := by
    have e1 : i * ((2 : ℝ)⁻¹ • (x + i * x * i))
        = algebraMap ℝ A ((2 : ℝ)⁻¹) * (i * (x + i * x * i)) := by
      rw [Algebra.smul_def, ← mul_assoc i _ _,
        ← (Algebra.commute_algebraMap_left ((2 : ℝ)⁻¹) i).eq, mul_assoc]
    have e2 : ((2 : ℝ)⁻¹ • (x + i * x * i)) * i
        = algebraMap ℝ A ((2 : ℝ)⁻¹) * ((x + i * x * i) * i) := by
      rw [Algebra.smul_def, mul_assoc]
    rw [e1, e2, key2, mul_neg]
  have hwcomm : (((2 : ℝ)⁻¹ • (x + i * x * i)) * j) * i
      = i * (((2 : ℝ)⁻¹ • (x + i * x * i)) * j) :=
    comm_of_anticomm_anticomm ha hji
  have hwcomm2 : (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * i
      = i * (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) := by
    rw [neg_mul, mul_neg, hwcomm]
  obtain ⟨z₂, hz₂⟩ := (AlgHom.mem_range _).mp
    (centralizer_eq_range hi _ hwcomm2)
  have ejj : (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j
      = (2 : ℝ)⁻¹ • (x + i * x * i) := by
    have e : ((((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j
        = ((2 : ℝ)⁻¹ • (x + i * x * i)) * (j * j) := mul_assoc _ _ _
    rw [neg_mul, e, hj, mul_neg, mul_one, neg_neg]
  have esum : ((2 : ℝ)⁻¹ • (x - i * x * i)) + ((2 : ℝ)⁻¹ • (x + i * x * i))
      = x := by
    have e : (x - i * x * i) + (x + i * x * i) = (2 : ℝ) • x := by
      rw [show (2 : ℝ) = 1 + 1 from one_add_one_eq_two.symm, add_smul,
        one_smul]
      abel
    rw [← smul_add, e, Algebra.smul_def, Algebra.smul_def,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2, map_one, one_mul]
  have hrec : x = ((2 : ℝ)⁻¹ • (x - i * x * i))
      + (-(((2 : ℝ)⁻¹ • (x + i * x * i)) * j)) * j := by
    rw [ejj]
    exact esum.symm
  have e1 : complexHom hi z₁ = (2 : ℝ)⁻¹ • (x - i * x * i) := hz₁
  have e2' : complexHom hi z₂ = -(((2 : ℝ)⁻¹ • (x + i * x * i)) * j) := hz₂
  rw [complexHom_apply hi z₁] at e1
  rw [complexHom_apply hi z₂] at e2'
  have ej : (algebraMap ℝ A z₂.re + z₂.im • i) * j
      = z₂.re • j + z₂.im • (i * j) := by
    have e : (algebraMap ℝ A z₂.re + z₂.im • i) * j
        = algebraMap ℝ A z₂.re * j + algebraMap ℝ A z₂.im * (i * j) := by
      rw [add_mul, Algebra.smul_def, mul_assoc]
    rw [e, ← Algebra.smul_def z₂.re j, ← Algebra.smul_def z₂.im (i * j)]
  refine ⟨QuaternionAlgebra.mk z₁.re z₁.im z₂.re z₂.im, ?_⟩
  rw [quatHom_mk, hrec, ← e1, add_assoc, ← ej, ← e2']

set_option linter.dupNamespace false in
/--
If `A` is a finite-dimensional associative unital division algebra over `ℝ` (`DivisionRing A`,
`Algebra ℝ A`, `FiniteDimensional ℝ A`), then `A` is `ℝ`-algebra isomorphic to `ℝ`, `ℂ`, or
`Quaternion ℝ`. Source: G. Frobenius, Ueber lineare Substitutionen und bilineare Formen,
J. reine angew. Math. 84 (1878), 1–63, DOI 10.1515/crelle-1878-18788403; textbook in Jacobson,
Basic Algebra II; Lean states associative unital case via `DivisionRing` excluding octonions
intentionally.

Proves `Wanted` entry `frobenius_real_division_algebra`.
-/
theorem frobenius_real_division_algebra
    {A : Type*} [DivisionRing A] [Algebra ℝ A] [FiniteDimensional ℝ A] :
    Nonempty (A ≃ₐ[ℝ] ℝ) ∨ Nonempty (A ≃ₐ[ℝ] ℂ) ∨ Nonempty (A ≃ₐ[ℝ] Quaternion ℝ) := by
  by_cases h1 : Module.finrank ℝ A = 1
  · exact Or.inl (equiv_real_of_finrank_one h1)
  · by_cases h2 : Module.finrank ℝ A = 2
    · obtain ⟨x, hx⟩ := exists_nonreal h1
      obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hx
      exact Or.inr (Or.inl
        (equiv_complex_of_finrank_two (complexHom hi) (complexHom_injective _)
          h2))
    · obtain ⟨x, hx⟩ := exists_nonreal h1
      obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hx
      have hex : ∃ w : A, w ∉ AlgHom.range (complexHom hi) := by
        by_contra hcon
        have hall : ∀ z : A, z ∈ AlgHom.range (complexHom hi) := by
          intro z
          by_contra hz
          apply hcon
          exact ⟨z, hz⟩
        have hsurj : Function.Surjective (complexHom hi) := by
          intro a
          exact (AlgHom.mem_range _).mp (hall a)
        have e := AlgEquiv.ofBijective (complexHom hi)
          ⟨complexHom_injective _, hsurj⟩
        have hfin := e.toLinearEquiv.finrank_eq
        rw [Complex.finrank_real_complex] at hfin
        exact h2 hfin.symm
      obtain ⟨w, hw⟩ := hex
      obtain ⟨j, hj, hanti⟩ := exists_anticommute hi hw
      have hbij : Function.Bijective (quatHom hi hj hanti) :=
        ⟨quatHom_injective _, quatHom_surjective hi hj hanti⟩
      exact Or.inr (Or.inr ⟨(AlgEquiv.ofBijective _ hbij).symm⟩)

end MathlibExt.Algebra.Algebra.FrobeniusDivisionWanted
