/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_TwoChartCech_Sections_finite_H0_of_chartFinite.lean`
and
`P2M/Sol/S_TwoChartCech_Sections_finite_H0_of_chartFinite.lean`,
with supporting material from
`Definitions/Def_AlgebraicGeometry_TwoChartCech.lean`,
`P2M/Sol/S_TwoChartCech_Sections_finite_H1_of_chartFinite.lean`
and
`P2M/Sol/S_TwoChartCech_kerMap_injective_of_H0_eq_zero.lean`
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

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finiteness of `H⁰` for a two-chart Čech complex

A two-chart cover of an `R`-scheme is modelled by three commutative `R`-algebras
`A0`, `A1`, `A01` with restriction maps `ρ0 : A0 →ₐ[R] A01` and `ρ1 : A1 →ₐ[R] A01`.
A quasi-coherent sheaf on it is modelled by modules `M0`, `M1`, `M01` with semilinear
restriction maps `r0`, `r1`. The Čech differential is `(s0, s1) ↦ r1 s1 - r0 s0`
and `H⁰` is its kernel.

The main result, `TwoChartCech.Sections.finite_H0_of_chartFinite`, shows that `H⁰` is a
finite `R`-module over a Noetherian ring `R` when the chart modules are finite over
`R[f]` and `R[g]` with `ρ0 f * ρ1 g = 1`, every overlap section is a restriction from
either chart after multiplying by a power of `ρ0 f`, resp. `ρ1 g`, and the kernels of
`r0`, `r1` are `f`-, resp. `g`-power torsion.

The proof follows Serre's argument on the projective line: the data are a quotient of a
finite free twisted module on `ℙ¹_R` whose `H⁰` vanishes, and the snake lemma embeds the
original `H⁰` into the `H¹` of the kernel, which is finite.
-/

universe u v w

@[expose] public section

namespace TwoChartCech

/-- A two-chart cover over `R`: the coordinate algebras of two charts and of their
overlap, with the restriction maps from each chart to the overlap. -/
structure Cover (R : Type u) [CommRing R] where
  /-- The coordinate algebra of the first chart. -/
  A0 : Type v
  /-- The coordinate algebra of the second chart. -/
  A1 : Type v
  /-- The coordinate algebra of the overlap. -/
  A01 : Type v
  [A0_commRing : CommRing A0]
  [A0_algebra : Algebra R A0]
  [A1_commRing : CommRing A1]
  [A1_algebra : Algebra R A1]
  [A01_commRing : CommRing A01]
  [A01_algebra : Algebra R A01]
  /-- Restriction from the first chart to the overlap. -/
  ρ0 : A0 →ₐ[R] A01
  /-- Restriction from the second chart to the overlap. -/
  ρ1 : A1 →ₐ[R] A01

attribute [instance] Cover.A0_commRing Cover.A0_algebra Cover.A1_commRing Cover.A1_algebra
  Cover.A01_commRing Cover.A01_algebra

/-- Sections of a module over a two-chart cover: modules over the two chart algebras and
over the overlap algebra, with restriction maps compatible with `ρ0` and `ρ1`. -/
structure Sections {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) where
  /-- Sections over the first chart. -/
  M0 : Type w
  /-- Sections over the second chart. -/
  M1 : Type w
  /-- Sections over the overlap. -/
  M01 : Type w
  [M0_addCommGroup : AddCommGroup M0]
  [M0_moduleA : Module 𝒰.A0 M0]
  [M0_module : Module R M0]
  [M0_tower : IsScalarTower R 𝒰.A0 M0]
  [M1_addCommGroup : AddCommGroup M1]
  [M1_moduleA : Module 𝒰.A1 M1]
  [M1_module : Module R M1]
  [M1_tower : IsScalarTower R 𝒰.A1 M1]
  [M01_addCommGroup : AddCommGroup M01]
  [M01_moduleA : Module 𝒰.A01 M01]
  [M01_module : Module R M01]
  [M01_tower : IsScalarTower R 𝒰.A01 M01]
  /-- Restriction of sections from the first chart to the overlap. -/
  r0 : M0 →ₗ[R] M01
  /-- Restriction of sections from the second chart to the overlap. -/
  r1 : M1 →ₗ[R] M01
  r0_smul : ∀ (a : 𝒰.A0) (m : M0), r0 (a • m) = 𝒰.ρ0 a • r0 m
  r1_smul : ∀ (a : 𝒰.A1) (m : M1), r1 (a • m) = 𝒰.ρ1 a • r1 m

attribute [instance] Sections.M0_addCommGroup Sections.M0_moduleA Sections.M0_module
  Sections.M0_tower Sections.M1_addCommGroup Sections.M1_moduleA Sections.M1_module
  Sections.M1_tower Sections.M01_addCommGroup Sections.M01_moduleA Sections.M01_module
  Sections.M01_tower

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

/-- The Čech differential `(s0, s1) ↦ r1 s1 - r0 s0`. -/
def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

theorem cechDiff_apply (s : S.M0 × S.M1) : S.cechDiff s = S.r1 s.2 - S.r0 s.1 := by
  simp [cechDiff, LinearMap.coprod_apply, sub_eq_neg_add]

/-- The Čech `H⁰`: pairs of chart sections that agree on the overlap. -/
abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

theorem mem_H0_iff (s : S.M0 × S.M1) : s ∈ S.H0 ↔ S.r0 s.1 = S.r1 s.2 := by
  rw [LinearMap.mem_ker, cechDiff_apply, sub_eq_zero, eq_comm]

end Sections

end TwoChartCech

end

/-! ### Auxiliary results, private to this file -/

namespace TwoChartCech

namespace ChartFinite

open Polynomial

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

private theorem vpow_mul_upow (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) (n j : ℕ) :
    𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j =
      if j ≤ n then 𝒰.ρ1 g ^ (n - j) else 𝒰.ρ0 f ^ (j - n) := by
  have hvu : 𝒰.ρ1 g * 𝒰.ρ0 f = 1 := by rw [mul_comm]; exact hfg
  induction n generalizing j with
  | zero => cases j <;> simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      have : 𝒰.ρ1 g ^ (n + 1) * 𝒰.ρ0 f ^ (j + 1) = 𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j := by
        rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (𝒰.ρ1 g) (𝒰.ρ0 f), hvu, one_mul]
      rw [this, ih j]
      simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ]

private noncomputable def gens (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : Finset S.M01 := by
  classical exact (s ×ˢ Finset.range N).image fun ek => 𝒰.ρ1 g ^ ek.2 • S.r0 ek.1

private noncomputable def W (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) : Submodule R S.M01 :=
  Submodule.span R (gens S g s N : Set S.M01) ⊔ LinearMap.range S.cechDiff

private theorem range_r0_le (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) :
    LinearMap.range S.r0 ≤ W S g s N := by
  rintro _ ⟨x, rfl⟩
  apply Submodule.mem_sup_right
  refine ⟨((-x : S.M0), (0 : S.M1)), ?_⟩
  rw [Sections.cechDiff_apply, map_zero, map_neg, zero_sub, neg_neg]

private theorem range_r1_le (g : 𝒰.A1) (s : Finset S.M0) (N : ℕ) :
    LinearMap.range S.r1 ≤ W S g s N := by
  rintro _ ⟨y, rfl⟩
  apply Submodule.mem_sup_right
  refine ⟨((0 : S.M0), y), ?_⟩
  rw [Sections.cechDiff_apply, map_zero, sub_zero]

private theorem vpow_smul_mem_range_r1 (g : 𝒰.A1) {m : S.M01} {n : ℕ}
    (h : 𝒰.ρ1 g ^ n • m ∈ LinearMap.range S.r1) (k : ℕ) (hk : n ≤ k) :
    𝒰.ρ1 g ^ k • m ∈ LinearMap.range S.r1 := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨g ^ d • y, ?_⟩
  rw [S.r1_smul, map_pow, hy, ← mul_smul, ← pow_add, add_comm]

private theorem upow_smul_r0_mem (f : 𝒰.A0) (x : S.M0) (i : ℕ) :
    𝒰.ρ0 f ^ i • S.r0 x ∈ LinearMap.range S.r0 :=
  ⟨f ^ i • x, by rw [S.r0_smul, map_pow]⟩

variable {S}

private theorem vpow_smul_r0_mem_W {g : 𝒰.A1} {s : Finset S.M0} {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1)
    {e : S.M0} (he : e ∈ s) (k : ℕ) : 𝒰.ρ1 g ^ k • S.r0 e ∈ W S g s N := by
  classical
  by_cases hk : k < N
  · apply Submodule.mem_sup_left
    apply Submodule.subset_span
    rw [gens, Finset.coe_image]
    exact ⟨(e, k), by simp [he, hk], rfl⟩
  · exact range_r1_le S g s N (vpow_smul_mem_range_r1 S g (hN e he) k (not_lt.mp hk))

private theorem vpow_smul_smul_mem_W {f : 𝒰.A0} {g : 𝒰.A1} (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    {s : Finset S.M0} {N : ℕ} {y : S.M01}
    (hv : ∀ i : ℕ, 𝒰.ρ1 g ^ i • y ∈ W S g s N) (hu : ∀ i : ℕ, 𝒰.ρ0 f ^ i • y ∈ W S g s N)
    (p : Algebra.adjoin R ({f} : Set 𝒰.A0)) (n : ℕ) :
    𝒰.ρ1 g ^ n • ((𝒰.ρ0 (p : 𝒰.A0)) • y) ∈ W S g s N := by
  have hp : (p : 𝒰.A0) ∈ (Polynomial.aeval (R := R) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact p.2
  obtain ⟨P, hP⟩ := hp
  rw [← hP]
  change 𝒰.ρ1 g ^ n • (𝒰.ρ0 (Polynomial.aeval f P) • y) ∈ _
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_eq_sum_range, Finset.sum_smul,
    Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hterm : 𝒰.ρ1 g ^ n • ((P.coeff j • 𝒰.ρ0 f ^ j) • y)
      = P.coeff j • ((𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ j) • y) := by
    rw [smul_assoc, smul_comm (𝒰.ρ1 g ^ n) (P.coeff j), ← mul_smul]
  rw [hterm, vpow_mul_upow f g hfg]
  refine Submodule.smul_mem _ _ ?_
  split_ifs
  · exact hv _
  · exact hu _

private theorem vpow_smul_r0_mem_W_of_mem_span {f : 𝒰.A0} {g : 𝒰.A1}
    (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) {s : Finset S.M0} {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1) {x : S.M0}
    (hx : x ∈ Submodule.span (Algebra.adjoin R ({f} : Set 𝒰.A0)) (s : Set S.M0)) (n : ℕ) :
    𝒰.ρ1 g ^ n • S.r0 x ∈ W S g s N := by
  induction hx using Submodule.span_induction generalizing n with
  | mem e he => exact vpow_smul_r0_mem_W hN he n
  | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ (hx n) (hy n)
  | smul p x _ hx =>
    have : S.r0 ((p : Algebra.adjoin R ({f} : Set 𝒰.A0)) • x) = 𝒰.ρ0 (p : 𝒰.A0) • S.r0 x := by
      rw [← S.r0_smul]; rfl
    rw [this]
    exact vpow_smul_smul_mem_W hfg hx
      (fun i => range_r0_le S g s N (upow_smul_r0_mem S f x i)) p n

private theorem W_eq_top {f : 𝒰.A0} {g : 𝒰.A1} (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1) {s : Finset S.M0}
    (hs : Submodule.span (Algebra.adjoin R ({f} : Set 𝒰.A0)) (s : Set S.M0) = ⊤) {N : ℕ}
    (hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, 𝒰.ρ0 f ^ n • m ∈ LinearMap.range S.r0) :
    W S g s N = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨n, x, hx⟩ := hloc0 m
  have hvu : 𝒰.ρ1 g ^ n * 𝒰.ρ0 f ^ n = 1 := by
    rw [vpow_mul_upow f g hfg]; simp
  have hm : m = 𝒰.ρ1 g ^ n • S.r0 x := by rw [hx, ← mul_smul, hvu, one_smul]
  rw [hm]
  exact vpow_smul_r0_mem_W_of_mem_span hfg hN (hs ▸ Submodule.mem_top) n

/-- Finiteness of the Čech `H¹` under the chart-finiteness and localization hypotheses. -/
private theorem finite_H1 (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1) :
    Module.Finite R (S.M01 ⧸ LinearMap.range S.cechDiff) := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin0
  choose nOf hnOf using fun m => hloc1 m
  let N : ℕ := s.sup fun e => nOf (S.r0 e)
  have hN : ∀ e ∈ s, 𝒰.ρ1 g ^ N • S.r0 e ∈ LinearMap.range S.r1 := fun e he =>
    vpow_smul_mem_range_r1 S g (hnOf (S.r0 e)) N (Finset.le_sup (f := fun e => nOf (S.r0 e)) he)
  have hW := W_eq_top (S := S) hfg hs hN hloc0
  refine Module.finite_def.mpr ⟨(gens S g s N).image (LinearMap.range S.cechDiff).mkQ, ?_⟩
  rw [Finset.coe_image, ← Submodule.map_span, eq_top_iff]
  rintro q -
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  have hm : m ∈ W S g s N := by rw [hW]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  have hb0 : (LinearMap.range S.cechDiff).mkQ b = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hb
  rw [map_add, hb0, add_zero]
  exact Submodule.mem_map_of_mem ha

end ChartFinite

namespace Snake

variable {R : Type*} [CommRing R] {K0 K1 E0 E1 S0 S1 : Type*}
    [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
    [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
    [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
    (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
    (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)

/-- The connecting map of the snake lemma embeds `ker dS` into `coker dK` when
`ker dE = 0`. -/
private theorem exists_injective_linearMap
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0)
    (hex1 : LinearMap.range i1 = LinearMap.ker p1) (hE : LinearMap.ker dE = ⊥) :
    ∃ δ : LinearMap.ker dS →ₗ[R] (K1 ⧸ LinearMap.range dK), Function.Injective δ := by
  classical
  have step : ∀ s : LinearMap.ker dS, ∃ k : K1, ∃ e : E0, p0 e = s ∧ dE e = i1 k := by
    intro s
    obtain ⟨e, he⟩ := hp0 s
    have : dE e ∈ LinearMap.ker p1 := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← hp, LinearMap.comp_apply, he]
      exact s.2
    rw [← hex1] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, e, he, hk.symm⟩
  choose kOf eOf hpe hde using step
  have well : ∀ (s : LinearMap.ker dS) (k : K1) (e : E0), p0 e = s → dE e = i1 k →
      (Submodule.Quotient.mk k : K1 ⧸ LinearMap.range dK) =
        Submodule.Quotient.mk (kOf s) := by
    intro s k e he hde'
    have hdiff : e - eOf s ∈ LinearMap.ker p0 := by
      rw [LinearMap.mem_ker, map_sub, he, hpe, sub_self]
    rw [← hex0] at hdiff
    obtain ⟨x, hx⟩ := hdiff
    rw [Submodule.Quotient.eq]
    refine ⟨x, hi1 ?_⟩
    have h1 : i1 (dK x) = dE (i0 x) := (LinearMap.congr_fun hi x).symm
    rw [h1, hx, map_sub, hde', hde, map_sub]
  refine ⟨
    { toFun := fun s => Submodule.Quotient.mk (kOf s)
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro s t
    change (Submodule.Quotient.mk (kOf (s + t)) : K1 ⧸ LinearMap.range dK)
      = Submodule.Quotient.mk (kOf s) + Submodule.Quotient.mk (kOf t)
    rw [← Submodule.Quotient.mk_add]
    exact (well (s + t) (kOf s + kOf t) (eOf s + eOf t)
      (by rw [map_add, hpe, hpe]; rfl) (by rw [map_add, hde, hde, map_add])).symm
  · intro r s
    change (Submodule.Quotient.mk (kOf (r • s)) : K1 ⧸ LinearMap.range dK) =
      r • Submodule.Quotient.mk (kOf s)
    rw [← Submodule.Quotient.mk_smul]
    exact (well (r • s) (r • kOf s) (r • eOf s)
      (by rw [map_smul, hpe]; rfl) (by rw [map_smul, hde, map_smul])).symm
  · intro s t hst
    have key : ∀ s : LinearMap.ker dS,
        (Submodule.Quotient.mk (kOf s) : K1 ⧸ LinearMap.range dK) = 0 → s = 0 := by
      intro s hs
      rw [Submodule.Quotient.mk_eq_zero] at hs
      obtain ⟨x, hx⟩ := hs
      have : eOf s - i0 x ∈ LinearMap.ker dE := by
        have h2 : dE (i0 x) = i1 (dK x) := LinearMap.congr_fun hi x
        rw [LinearMap.mem_ker, map_sub, hde, ← hx, h2, sub_self]
      rw [hE, Submodule.mem_bot, sub_eq_zero] at this
      apply Subtype.ext
      rw [← hpe s, this]
      have : p0 (i0 x) = 0 := by
        have hmem : i0 x ∈ LinearMap.ker p0 := by
          rw [← hex0]; exact LinearMap.mem_range_self _ _
        exact hmem
      rw [this]; rfl
    have hsub : (Submodule.Quotient.mk (kOf (s - t)) : K1 ⧸ LinearMap.range dK)
        = Submodule.Quotient.mk (kOf s) - Submodule.Quotient.mk (kOf t) := by
      rw [← Submodule.Quotient.mk_sub]
      exact (well (s - t) (kOf s - kOf t) (eOf s - eOf t)
        (by rw [map_sub, hpe, hpe]; rfl) (by rw [map_sub, hde, hde, map_sub])).symm
    have h0 : (Submodule.Quotient.mk (kOf (s - t)) : K1 ⧸ LinearMap.range dK) = 0 := by
      rw [hsub]; exact sub_eq_zero.mpr hst
    exact sub_eq_zero.mp (key (s - t) h0)

private theorem finite_ker [IsNoetherianRing R]
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0)
    (hex1 : LinearMap.range i1 = LinearMap.ker p1) (hE : LinearMap.ker dE = ⊥)
    [Module.Finite R (K1 ⧸ LinearMap.range dK)] :
    Module.Finite R (LinearMap.ker dS) := by
  obtain ⟨δ, hδ⟩ :=
    exists_injective_linearMap dK dE dS i0 i1 p0 p1 hi hp hi1 hp0 hex0 hex1 hE
  exact Module.Finite.of_injective δ hδ

end Snake

namespace SerreH0

open Polynomial LaurentPolynomial

section P1

variable (R : Type u) [CommRing R]

/-- The standard two-chart cover of the projective line over `R`. -/
@[reducible] private noncomputable def P1Cover : Cover.{u, u} R where
  A0 := R[X]
  A1 := R[X]
  A01 := R[T;T⁻¹]
  ρ0 := Polynomial.toLaurentAlg
  ρ1 := (LaurentPolynomial.invert (R := R)).toAlgHom.comp Polynomial.toLaurentAlg

/-- The free sheaf `𝒪(-a)^m` on the projective line, as two-chart sections. -/
@[reducible] private noncomputable def twistSections (m a : ℕ) :
    Sections.{u, u, u} (P1Cover R) where
  M0 := Fin m → R[X]
  M1 := Fin m → R[X]
  M01 := Fin m → R[T;T⁻¹]
  r0 :=
    { toFun := fun v i => Polynomial.toLaurent (v i)
      map_add' := fun v w => funext fun i => map_add _ _ _
      map_smul' := fun r v => funext fun i => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact map_smul (Polynomial.toLaurentAlg (R := R)) r (v i) }
  r1 :=
    { toFun := fun v i =>
        T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i))
      map_add' := fun v w => funext fun i => by
        simp only [Pi.add_apply, map_add, mul_add]
      map_smul' := fun r v => funext fun i => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        have h1 : Polynomial.toLaurent (r • v i) = r • Polynomial.toLaurent (v i) :=
          map_smul (Polynomial.toLaurentAlg (R := R)) r (v i)
        rw [h1, map_smul, mul_smul_comm] }
  r0_smul p v := funext fun i => by
    change Polynomial.toLaurent ((p • v) i) = Polynomial.toLaurent p * Polynomial.toLaurent (v i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  r1_smul p v := funext fun i => by
    change T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent ((p • v) i))
      = LaurentPolynomial.invert (Polynomial.toLaurent p)
          * (T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i)))
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

end P1

variable {R : Type u} [CommRing R]

private theorem twistSections_r1_apply (m a : ℕ) (v : Fin m → R[X]) (i : Fin m) :
    ((twistSections R m a).r1 v : Fin m → R[T;T⁻¹]) i
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (v i)) := rfl

private theorem twistSections_cechDiff_apply (m a : ℕ)
    (p : (Fin m → R[X]) × (Fin m → R[X])) (i : Fin m) :
    ((twistSections R m a).cechDiff p : Fin m → R[T;T⁻¹]) i
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (p.2 i))
        - Polynomial.toLaurent (p.1 i) := by
  rw [Sections.cechDiff_apply]; rfl

private theorem toLaurent_coeff_natCast (p : R[X]) (k : ℕ) :
    (Polynomial.toLaurent p : R[T;T⁻¹]).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent, ← Polynomial.toFinsupp_apply]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ k

private theorem toLaurent_coeff_of_neg (p : R[X]) {n : ℤ} (hn : n < 0) :
    (Polynomial.toLaurent p : R[T;T⁻¹]).coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, rfl⟩
  exact (not_le.mpr hn) (Int.natCast_nonneg k)

private theorem T_mul_coeff (n : ℤ) (f : R[T;T⁻¹]) (k : ℤ) :
    (T n * f : R[T;T⁻¹]).coeff k = f.coeff (k - n) := by
  have : (T n * f : R[T;T⁻¹]) = AddMonoidAlgebra.single n (1 : R) * f := rfl
  rw [this, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (k - n)]
  · rw [one_mul]
  · intro a _
    omega

private theorem eq_zero_of_toLaurent_eq_T_neg_mul_invert {a : ℕ} (ha : 1 ≤ a) {p q : R[X]}
    (h : (Polynomial.toLaurent p : R[T;T⁻¹])
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent q)) :
    p = 0 ∧ q = 0 := by
  have hcoef : ∀ n : ℤ, (Polynomial.toLaurent p : R[T;T⁻¹]).coeff n
      = (Polynomial.toLaurent q : R[T;T⁻¹]).coeff (-(n + a)) := by
    intro n
    rw [h, T_mul_coeff, LaurentPolynomial.invert_apply]
    congr 1
    omega
  constructor
  · apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero, ← toLaurent_coeff_natCast, hcoef]
    exact toLaurent_coeff_of_neg q (by omega)
  · apply Polynomial.ext
    intro k
    have := hcoef (-((k : ℤ) + a))
    rw [show (-(-((k : ℤ) + a) + a)) = (k : ℤ) by omega, toLaurent_coeff_natCast] at this
    rw [Polynomial.coeff_zero, ← this]
    exact toLaurent_coeff_of_neg p (by omega)

/-- `H⁰(ℙ¹, 𝒪(-a)^m) = 0` for `a ≥ 1`. -/
private theorem ker_cechDiff_twistSections_eq_bot (m a : ℕ) (ha : 1 ≤ a) :
    LinearMap.ker (twistSections R m a).cechDiff = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨v, w⟩ hvw
  have h : ∀ i, (Polynomial.toLaurent (v i) : R[T;T⁻¹])
      = T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (w i)) := by
    intro i
    have := congrFun hvw i
    rw [twistSections_cechDiff_apply] at this
    change T (-(a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (w i)) -
      Polynomial.toLaurent (v i) = (0 : R[T;T⁻¹]) at this
    rw [sub_eq_zero] at this
    exact this.symm
  apply Prod.ext
  · funext i; exact (eq_zero_of_toLaurent_eq_T_neg_mul_invert ha (h i)).1
  · funext i; exact (eq_zero_of_toLaurent_eq_T_neg_mul_invert ha (h i)).2

section evalUnit

variable {A : Type*} [CommRing A] [Algebra R A] (u : A) (hu : IsUnit u)

/-- Evaluation of Laurent polynomials at a unit. -/
private noncomputable def evalUnit : R[T;T⁻¹] →+* A :=
  IsLocalization.Away.lift (X : R[X]) (g := (Polynomial.aeval u : R[X] →ₐ[R] A).toRingHom)
    (by simpa using hu)

private theorem evalUnit_toLaurent (p : R[X]) :
    evalUnit u hu (Polynomial.toLaurent p) = Polynomial.aeval u p := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.Away.lift_eq (X : R[X]) _ p

private theorem evalUnit_C (r : R) : evalUnit u hu (LaurentPolynomial.C r) = algebraMap R A r := by
  rw [← Polynomial.toLaurent_C, evalUnit_toLaurent, Polynomial.aeval_C]

private theorem evalUnit_algebraMap (r : R) :
    evalUnit u hu (algebraMap R R[T;T⁻¹] r) = algebraMap R A r := by
  have : algebraMap R R[T;T⁻¹] r = LaurentPolynomial.C r := by
    rfl
  rw [this, evalUnit_C]

private noncomputable def evalUnitAlg : R[T;T⁻¹] →ₐ[R] A :=
  { evalUnit u hu with commutes' := evalUnit_algebraMap u hu }

private theorem evalUnitAlg_apply (ℓ : R[T;T⁻¹]) : evalUnitAlg u hu ℓ = evalUnit u hu ℓ := rfl

private theorem evalUnit_T_one : evalUnit u hu (T 1 : R[T;T⁻¹]) = u := by
  rw [← Polynomial.toLaurent_X, evalUnit_toLaurent, Polynomial.aeval_X]

private theorem evalUnit_T_natCast (n : ℕ) :
    evalUnit u hu (T (n : ℤ) : R[T;T⁻¹]) = u ^ n := by
  rw [← Polynomial.toLaurent_X_pow, evalUnit_toLaurent, map_pow, Polynomial.aeval_X]

private theorem evalUnit_T_neg_one_mul : evalUnit u hu (T (-1) : R[T;T⁻¹]) * u = 1 := by
  have : evalUnit u hu (T (-1) : R[T;T⁻¹]) * evalUnit u hu (T 1 : R[T;T⁻¹]) = 1 := by
    rw [← map_mul, ← T_add]
    change evalUnit u hu (T 0 : R[T;T⁻¹]) = 1
    rw [LaurentPolynomial.T_zero, map_one]
  rwa [evalUnit_T_one] at this

private theorem evalUnit_smul (r : R) (ℓ : R[T;T⁻¹]) :
    evalUnit u hu (r • ℓ) = r • evalUnit u hu ℓ :=
  map_smul (evalUnitAlg u hu) r ℓ

private theorem evalUnit_invert_toLaurent {w : A} (hw : u * w = 1) (p : R[X]) :
    evalUnit u hu (LaurentPolynomial.invert (Polynomial.toLaurent p)) =
      Polynomial.aeval w p := by
  have key : ((evalUnitAlg u hu).comp ((LaurentPolynomial.invert (R := R)).toAlgHom.comp
      Polynomial.toLaurentAlg)) = Polynomial.aeval w := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
      Polynomial.aeval_X, evalUnitAlg_apply]
    have h1 := evalUnit_T_neg_one_mul (R := R) u hu
    calc evalUnit u hu (T (-1) : R[T;T⁻¹])
        = evalUnit u hu (T (-1) : R[T;T⁻¹]) * (u * w) := by rw [hw, mul_one]
      _ = (evalUnit u hu (T (-1) : R[T;T⁻¹]) * u) * w := by ring
      _ = w := by rw [h1, one_mul]
  have := congrArg (fun F : R[X] →ₐ[R] A => F p) key
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Polynomial.toLaurentAlg_apply, evalUnitAlg_apply] using this

end evalUnit

variable {𝒰 : Cover.{u, v} R}

/-- A presentation of chart sections as a quotient of the free twisted sheaf
`𝒪(-a)^m` on the projective line, compatible with all restriction maps. -/
private structure SerreData (S : Sections.{u, v, w} 𝒰) (f : 𝒰.A0) (g : 𝒰.A1) where
  m : ℕ
  a : ℕ
  one_le_a : 1 ≤ a
  hu : IsUnit (𝒰.ρ0 f)
  π0 : (Fin m → R[X]) →ₗ[R] S.M0
  π1 : (Fin m → R[X]) →ₗ[R] S.M1
  π01 : (Fin m → R[T;T⁻¹]) →ₗ[R] S.M01
  π0_smul : ∀ (p : R[X]) (v : Fin m → R[X]), π0 (p • v) = Polynomial.aeval f p • π0 v
  π1_smul : ∀ (p : R[X]) (v : Fin m → R[X]), π1 (p • v) = Polynomial.aeval g p • π1 v
  π01_smul : ∀ (ℓ : R[T;T⁻¹]) (w : Fin m → R[T;T⁻¹]),
    π01 (ℓ • w) = evalUnit (𝒰.ρ0 f) hu ℓ • π01 w
  comm0 : S.r0 ∘ₗ π0 = π01 ∘ₗ (twistSections R m a).r0
  comm1 : S.r1 ∘ₗ π1 = π01 ∘ₗ (twistSections R m a).r1
  surj0 : Function.Surjective π0
  surj1 : Function.Surjective π1
  surj01 : Function.Surjective π01

namespace SerreData

variable {S : Sections.{u, v, w} 𝒰} {f : 𝒰.A0} {g : 𝒰.A1} (D : SerreData S f g)

private noncomputable def K0 : Submodule R[X] (Fin D.m → R[X]) where
  carrier := {v | D.π0 v = 0}
  add_mem' {v w} (hv : D.π0 v = 0) (hw : D.π0 w = 0) := by
    change D.π0 (v + w) = 0
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by change D.π0 0 = 0; exact map_zero _
  smul_mem' p v (hv : D.π0 v = 0) := by
    change D.π0 (p • v) = 0
    rw [D.π0_smul, hv, smul_zero]

private noncomputable def K1 : Submodule R[X] (Fin D.m → R[X]) where
  carrier := {v | D.π1 v = 0}
  add_mem' {v w} (hv : D.π1 v = 0) (hw : D.π1 w = 0) := by
    change D.π1 (v + w) = 0
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by change D.π1 0 = 0; exact map_zero _
  smul_mem' p v (hv : D.π1 v = 0) := by
    change D.π1 (p • v) = 0
    rw [D.π1_smul, hv, smul_zero]

private noncomputable def K01 : Submodule R[T;T⁻¹] (Fin D.m → R[T;T⁻¹]) where
  carrier := {v | D.π01 v = 0}
  add_mem' {v w} (hv : D.π01 v = 0) (hw : D.π01 w = 0) := by
    change D.π01 (v + w) = 0
    rw [map_add, hv, hw, add_zero]
  zero_mem' := by change D.π01 0 = 0; exact map_zero _
  smul_mem' p v (hv : D.π01 v = 0) := by
    change D.π01 (p • v) = 0
    rw [D.π01_smul, hv, smul_zero]

private theorem mem_K0_iff (v) : v ∈ D.K0 ↔ D.π0 v = 0 := Iff.rfl
private theorem mem_K1_iff (v) : v ∈ D.K1 ↔ D.π1 v = 0 := Iff.rfl
private theorem mem_K01_iff (w) : w ∈ D.K01 ↔ D.π01 w = 0 := Iff.rfl

private theorem r0_mem_K01 {v} (hv : v ∈ D.K0) : (twistSections R D.m D.a).r0 v ∈ D.K01 := by
  rw [mem_K01_iff]
  have := congrArg (fun F => F v) D.comm0
  simp only [LinearMap.comp_apply] at this
  rw [← this, (D.mem_K0_iff v).mp hv, map_zero]

private theorem r1_mem_K01 {v} (hv : v ∈ D.K1) : (twistSections R D.m D.a).r1 v ∈ D.K01 := by
  rw [mem_K01_iff]
  have := congrArg (fun F => F v) D.comm1
  simp only [LinearMap.comp_apply] at this
  rw [← this, (D.mem_K1_iff v).mp hv, map_zero]

/-- The kernel of the presentation, as two-chart sections on the projective line. -/
@[reducible] private noncomputable def kerSections : Sections.{u, u, u} (P1Cover R) where
  M0 := ↥D.K0
  M1 := ↥D.K1
  M01 := ↥D.K01
  r0 :=
    { toFun := fun v => ⟨(twistSections R D.m D.a).r0 (v : Fin D.m → R[X]), D.r0_mem_K01 v.2⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun r v => Subtype.ext (by
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply]
        exact map_smul _ r (v : Fin D.m → R[X])) }
  r1 :=
    { toFun := fun v => ⟨(twistSections R D.m D.a).r1 (v : Fin D.m → R[X]), D.r1_mem_K01 v.2⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun r v => Subtype.ext (by
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply]
        exact map_smul _ r (v : Fin D.m → R[X])) }
  r0_smul p v := Subtype.ext ((twistSections R D.m D.a).r0_smul p (v : Fin D.m → R[X]))
  r1_smul p v := Subtype.ext ((twistSections R D.m D.a).r1_smul p (v : Fin D.m → R[X]))

end SerreData

private theorem eq_of_mul_eq_one_of_mul_eq_one {A : Type*} [CommMonoid A] {x y z : A}
    (hx : x * z = 1) (hy : y * z = 1) : x = y := by
  calc x = x * (y * z) := by rw [hy, mul_one]
    _ = y * (x * z) := by rw [mul_left_comm]
    _ = y := by rw [hx, mul_one]

private theorem exists_generators_aeval {A : Type*} [CommRing A] [Algebra R A] (a : A)
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (hfin : Module.Finite (Algebra.adjoin R ({a} : Set A)) M) :
    ∃ (p : ℕ) (e : Fin p → M), ∀ x : M, ∃ c : Fin p → R[X],
      x = ∑ i, Polynomial.aeval a (c i) • e i := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.card, fun i => (s.equivFin.symm i : M), fun x => ?_⟩
  have hx : x ∈ Submodule.span (Algebra.adjoin R ({a} : Set A))
      (Set.range fun i => ((s.equivFin.symm i : ↥s) : M)) := by
    have hrange : (Set.range fun i => ((s.equivFin.symm i : ↥s) : M)) = (s : Set M) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
      · intro hy; exact ⟨s.equivFin ⟨y, hy⟩, by simp⟩
    rw [hrange, hs]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  have hc' : ∀ i, ∃ q : R[X],
      ((c i : Algebra.adjoin R ({a} : Set A)) : A) = Polynomial.aeval a q := by
    intro i
    have : ((c i : Algebra.adjoin R ({a} : Set A)) : A) ∈
        (Polynomial.aeval a : R[X] →ₐ[R] A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (c i).2
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  choose q hq using hc'
  refine ⟨q, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hq i]
  rfl

variable {S : Sections.{u, v, w} 𝒰} {f : 𝒰.A0} {g : 𝒰.A1}

private theorem exists_serreData (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1) :
    Nonempty (SerreData S f g) := by
  classical
  set u : 𝒰.A01 := 𝒰.ρ0 f with hudef
  set w : 𝒰.A01 := 𝒰.ρ1 g with hwdef
  have huw : u * w = 1 := hfg
  have hwu : w * u = 1 := by rw [mul_comm]; exact hfg
  have hu : IsUnit u := ⟨⟨u, w, huw, hwu⟩, rfl⟩
  obtain ⟨p, e, he⟩ := exists_generators_aeval f S.M0 hfin0
  obtain ⟨q, t, ht⟩ := exists_generators_aeval g S.M1 hfin1
  choose n hn using fun j => hloc0 (S.r1 (t j))
  choose n' hn' using fun i => hloc1 (S.r0 (e i))
  choose x hx using fun j => LinearMap.mem_range.mp (hn j)
  choose x' hx' using fun i => LinearMap.mem_range.mp (hn' i)
  let a : ℕ := 1 + (∑ j, n j) + (∑ i, n' i)
  have ha : 1 ≤ a := by omega
  have hna : ∀ j, n j ≤ a := fun j => by
    have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hn'a : ∀ i, n' i ≤ a := fun i => by
    have := Finset.single_le_sum (f := n') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  let y : Fin q → S.M0 := fun j => f ^ (a - n j) • x j
  let z : Fin p → S.M1 := fun i => g ^ (a - n' i) • x' i
  have hy : ∀ j, S.r0 (y j) = u ^ a • S.r1 (t j) := by
    intro j
    change S.r0 (f ^ (a - n j) • x j) = _
    rw [S.r0_smul, map_pow, hx j, ← hudef, smul_smul, ← pow_add, Nat.sub_add_cancel (hna j)]
  have hz : ∀ i, S.r1 (z i) = w ^ a • S.r0 (e i) := by
    intro i
    change S.r1 (g ^ (a - n' i) • x' i) = _
    rw [S.r1_smul, map_pow, hx' i, ← hwdef, smul_smul, ← pow_add,
      Nat.sub_add_cancel (hn'a i)]
  let m := p + q
  let t0 : Fin m → S.M0 := Fin.append e y
  let t1 : Fin m → S.M1 := Fin.append z t
  let c : Fin m → S.M01 := Fin.append (fun i => S.r0 (e i)) (fun j => u ^ a • S.r1 (t j))
  have hwaua : w ^ a * u ^ a = 1 := by rw [← mul_pow, hwu, one_pow]
  have ht0 : ∀ k, S.r0 (t0 k) = c k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [t0, c, Fin.append_left]
    · simp only [t0, c, Fin.append_right, hy]
  have ht1 : ∀ k, S.r1 (t1 k) = w ^ a • c k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [t1, c, Fin.append_left, hz]
    · simp only [t1, c, Fin.append_right, smul_smul, hwaua, one_smul]
  have hevT : ∀ k : ℕ, evalUnit u hu (T (-(k : ℤ)) : R[T;T⁻¹]) = w ^ k := by
    intro k
    apply eq_of_mul_eq_one_of_mul_eq_one (z := u ^ k)
    · rw [← evalUnit_T_natCast (R := R) u hu k, ← map_mul, ← T_add]
      have h0 : (-(k : ℤ) + k) = 0 := by omega
      rw [h0, LaurentPolynomial.T_zero, map_one]
    · rw [← mul_pow, hwu, one_pow]
  let π0 : (Fin m → R[X]) →ₗ[R] S.M0 :=
    { toFun := fun v => ∑ k, Polynomial.aeval f (v k) • t0 k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, map_smul, smul_assoc] }
  let π1 : (Fin m → R[X]) →ₗ[R] S.M1 :=
    { toFun := fun v => ∑ k, Polynomial.aeval g (v k) • t1 k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, map_smul, smul_assoc] }
  let π01 : (Fin m → R[T;T⁻¹]) →ₗ[R] S.M01 :=
    { toFun := fun v => ∑ k, evalUnit u hu (v k) • c k
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.add_apply, map_add, add_smul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, evalUnit_smul, smul_assoc] }
  have π0_apply : ∀ v, π0 v = ∑ k, Polynomial.aeval f (v k) • t0 k := fun _ => rfl
  have π1_apply : ∀ v, π1 v = ∑ k, Polynomial.aeval g (v k) • t1 k := fun _ => rfl
  have π01_apply : ∀ v, π01 v = ∑ k, evalUnit u hu (v k) • c k := fun _ => rfl
  have hπ0_smul : ∀ (P : R[X]) (v : Fin m → R[X]),
      π0 (P • v) = Polynomial.aeval f P • π0 v := by
    intro P v
    rw [π0_apply, π0_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hπ1_smul : ∀ (P : R[X]) (v : Fin m → R[X]),
      π1 (P • v) = Polynomial.aeval g P • π1 v := by
    intro P v
    rw [π1_apply, π1_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hπ01_smul : ∀ (ℓ : R[T;T⁻¹]) (v : Fin m → R[T;T⁻¹]),
      π01 (ℓ • v) = evalUnit u hu ℓ • π01 v := by
    intro ℓ v
    rw [π01_apply, π01_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  have hcomm0 : S.r0 ∘ₗ π0 = π01 ∘ₗ (twistSections R m a).r0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, π0_apply, π01_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S.r0_smul, ht0 k, ← Polynomial.aeval_algHom_apply, ← hudef]
    congr 1
    exact (evalUnit_toLaurent u hu (v k)).symm
  have hcomm1 : S.r1 ∘ₗ π1 = π01 ∘ₗ (twistSections R m a).r1 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, π1_apply, π01_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [S.r1_smul, ht1 k, ← Polynomial.aeval_algHom_apply, ← hwdef, smul_smul]
    rw [twistSections_r1_apply]
    congr 1
    rw [map_mul, hevT a, evalUnit_invert_toLaurent u hu huw, mul_comm]
  have hsurj0 : Function.Surjective π0 := by
    intro xm
    obtain ⟨cf, hcf⟩ := he xm
    refine ⟨Fin.append cf 0, ?_⟩
    rw [π0_apply, hcf, Fin.sum_univ_add]
    simp only [t0, Fin.append_left, Fin.append_right, Pi.zero_apply, map_zero, zero_smul,
      Finset.sum_const_zero, add_zero]
  have hsurj1 : Function.Surjective π1 := by
    intro xm
    obtain ⟨cg, hcg⟩ := ht xm
    refine ⟨Fin.append 0 cg, ?_⟩
    rw [π1_apply, hcg, Fin.sum_univ_add]
    simp only [t1, Fin.append_left, Fin.append_right, Pi.zero_apply, map_zero, zero_smul,
      Finset.sum_const_zero, zero_add]
  have hsurj01 : Function.Surjective π01 := by
    intro mv
    obtain ⟨N, hN⟩ := hloc0 mv
    obtain ⟨x0, hx0⟩ := LinearMap.mem_range.mp hN
    obtain ⟨v, rfl⟩ := hsurj0 x0
    have hc0v : S.r0 (π0 v) = π01 ((twistSections R m a).r0 v) := by
      have := congrArg (fun F => F v) hcomm0
      simpa only [LinearMap.comp_apply] using this
    refine ⟨(T (-(N : ℤ)) : R[T;T⁻¹]) • (twistSections R m a).r0 v, ?_⟩
    have hwNuN : w ^ N * u ^ N = 1 := by rw [← mul_pow, hwu, one_pow]
    rw [hπ01_smul, hevT N, ← hc0v, hx0, smul_smul, hwNuN, one_smul]
  exact ⟨⟨m, a, ha, hu, π0, π1, π01, hπ0_smul, hπ1_smul, hπ01_smul, hcomm0, hcomm1,
    hsurj0, hsurj1, hsurj01⟩⟩

namespace SerreData

variable (D : SerreData S f g)

private theorem kerSections_hfin0 [IsNoetherianRing R] :
    Module.Finite (Algebra.adjoin R ({X} : Set (P1Cover R).A0)) D.kerSections.M0 := by
  have hKfg : D.K0.FG := IsNoetherian.noetherian D.K0
  have : Module.Finite R[X] ↥D.K0 := Module.Finite.iff_fg.mpr hKfg
  have : Module.Finite (Algebra.adjoin R ({X} : Set R[X])) R[X] := by
    refine ⟨⟨{1}, ?_⟩⟩
    rw [Finset.coe_singleton, eq_top_iff]
    rintro p -
    have hp : p ∈ Algebra.adjoin R ({X} : Set R[X]) := by
      rw [Polynomial.adjoin_X]; exact Algebra.mem_top
    have : p = (⟨p, hp⟩ : Algebra.adjoin R ({X} : Set R[X])) • (1 : R[X]) := by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  exact Module.Finite.trans R[X] ↥D.K0

private theorem exists_T_pow_smul_eq (m : ℕ) (kv : Fin m → R[T;T⁻¹]) :
    ∃ (N : ℕ) (ev : Fin m → R[X]), ∀ i, T (N : ℤ) * kv i = Polynomial.toLaurent (ev i) := by
  choose Nf ef hef using fun i => (kv i).exists_T_pow
  refine ⟨∑ i, Nf i, fun i => ef i * X ^ ((∑ i, Nf i) - Nf i), fun i => ?_⟩
  have hle : Nf i ≤ ∑ i, Nf i :=
    Finset.single_le_sum (f := Nf) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [map_mul, hef, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_assoc,
    ← T_add, mul_comm]
  congr 2
  push_cast [Nat.cast_sub hle]
  ring

private theorem kerSections_hloc0
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0) :
    ∀ k : D.kerSections.M01, ∃ n : ℕ,
      ((P1Cover R).ρ0 X) ^ n • k ∈ LinearMap.range D.kerSections.r0 := by
  rintro ⟨kv, hk⟩
  obtain ⟨N, ev, hev⟩ := exists_T_pow_smul_eq D.m kv
  have hr0ev : (twistSections R D.m D.a).r0 ev = (T (N : ℤ) : R[T;T⁻¹]) • kv := by
    funext i
    change Polynomial.toLaurent (ev i) = T (N : ℤ) * kv i
    exact (hev i).symm
  have hc0 : S.r0 (D.π0 ev) = 0 := by
    have := congrArg (fun F => F ev) D.comm0
    simp only [LinearMap.comp_apply] at this
    rw [this, hr0ev, D.π01_smul, (D.mem_K01_iff kv).mp hk, smul_zero]
  obtain ⟨M, hM⟩ := htors0 _ hc0
  have hmem : (X : R[X]) ^ M • ev ∈ D.K0 := by
    rw [mem_K0_iff, D.π0_smul, map_pow, Polynomial.aeval_X, hM]
  refine ⟨M + N, ⟨⟨(X : R[X]) ^ M • ev, hmem⟩, Subtype.ext ?_⟩⟩
  change (twistSections R D.m D.a).r0 ((X : R[X]) ^ M • ev) =
    ((P1Cover R).ρ0 X) ^ (M + N) • kv
  rw [(twistSections R D.m D.a).r0_smul, hr0ev, map_pow, smul_smul]
  congr 1
  change Polynomial.toLaurent (X : R[X]) ^ M * T (N : ℤ) =
    Polynomial.toLaurent (X : R[X]) ^ (M + N)
  rw [Polynomial.toLaurent_X, LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← T_add]
  congr 1
  push_cast
  ring

private theorem kerSections_hloc1
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    ∀ k : D.kerSections.M01, ∃ n : ℕ,
      ((P1Cover R).ρ1 X) ^ n • k ∈ LinearMap.range D.kerSections.r1 := by
  rintro ⟨kv, hk⟩
  obtain ⟨N, ev, hev⟩ :=
    exists_T_pow_smul_eq D.m (fun i => LaurentPolynomial.invert (kv i))
  have hev' : ∀ i, LaurentPolynomial.invert (Polynomial.toLaurent (ev i)) =
      T (-(N : ℤ)) * kv i := by
    intro i
    rw [← hev i, map_mul, LaurentPolynomial.invert_T]
    congr 1
    exact LaurentPolynomial.invert.apply_symm_apply (kv i)
  have hr1ev : (twistSections R D.m D.a).r1 ev =
      (T (-((N : ℤ) + D.a)) : R[T;T⁻¹]) • kv := by
    funext i
    change T (-(D.a : ℤ)) * LaurentPolynomial.invert (Polynomial.toLaurent (ev i)) =
      T (-((N : ℤ) + D.a)) * kv i
    rw [hev', ← mul_assoc, ← T_add]
    congr 2
    ring
  have hc1 : S.r1 (D.π1 ev) = 0 := by
    have := congrArg (fun F => F ev) D.comm1
    simp only [LinearMap.comp_apply] at this
    rw [this, hr1ev, D.π01_smul, (D.mem_K01_iff kv).mp hk, smul_zero]
  obtain ⟨M, hM⟩ := htors1 _ hc1
  have hmem : (X : R[X]) ^ M • ev ∈ D.K1 := by
    rw [mem_K1_iff, D.π1_smul, map_pow, Polynomial.aeval_X, hM]
  refine ⟨M + N + D.a, ⟨⟨(X : R[X]) ^ M • ev, hmem⟩, Subtype.ext ?_⟩⟩
  change (twistSections R D.m D.a).r1 ((X : R[X]) ^ M • ev) =
    ((P1Cover R).ρ1 X) ^ (M + N + D.a) • kv
  rw [(twistSections R D.m D.a).r1_smul, hr1ev, map_pow, smul_smul]
  congr 1
  change (LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X]))) ^ M *
      T (-((N : ℤ) + D.a)) =
    (LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X]))) ^ (M + N + D.a)
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, LaurentPolynomial.T_pow,
    LaurentPolynomial.T_pow, ← T_add]
  congr 1
  push_cast
  ring

end SerreData

private theorem P1Cover_hfg : (P1Cover R).ρ0 X * (P1Cover R).ρ1 X = 1 := by
  change Polynomial.toLaurent (X : R[X]) *
    LaurentPolynomial.invert (Polynomial.toLaurent (X : R[X])) = 1
  rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, ← T_add]
  simp

namespace SerreData

private theorem finite_H0 [IsNoetherianRing R] (D : SerreData S f g)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 := by
  have hK1 : Module.Finite R
      (D.kerSections.M01 ⧸ LinearMap.range D.kerSections.cechDiff) :=
    ChartFinite.finite_H1 (S := D.kerSections) X X P1Cover_hfg
      D.kerSections_hfin0 (D.kerSections_hloc0 htors0) (D.kerSections_hloc1 htors1)
  let E := twistSections R D.m D.a
  let i0 : D.kerSections.M0 × D.kerSections.M1 →ₗ[R] E.M0 × E.M1 :=
    LinearMap.prodMap (D.K0.subtype.restrictScalars R) (D.K1.subtype.restrictScalars R)
  let i1 : D.kerSections.M01 →ₗ[R] E.M01 := D.K01.subtype.restrictScalars R
  let p0 : E.M0 × E.M1 →ₗ[R] S.M0 × S.M1 := LinearMap.prodMap D.π0 D.π1
  let p1 : E.M01 →ₗ[R] S.M01 := D.π01
  have hi : E.cechDiff ∘ₗ i0 = i1 ∘ₗ D.kerSections.cechDiff := by
    apply LinearMap.ext; intro x; rfl
  have hp : S.cechDiff ∘ₗ p0 = p1 ∘ₗ E.cechDiff := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, Sections.cechDiff_apply, map_sub]
    have h0 := congrArg (fun F => F v) D.comm0
    have h1 := congrArg (fun F => F w) D.comm1
    simp only [LinearMap.comp_apply] at h0 h1
    change S.r1 (D.π1 w) - S.r0 (D.π0 v) = D.π01 (E.r1 w) - D.π01 (E.r0 v)
    rw [h0, h1]
  have hi1 : Function.Injective i1 := fun x y hxy => Subtype.ext hxy
  have hp0 : Function.Surjective p0 := fun ⟨x, y⟩ => by
    obtain ⟨v, rfl⟩ := D.surj0 x
    obtain ⟨w, rfl⟩ := D.surj1 y
    exact ⟨(v, w), rfl⟩
  have hex0 : LinearMap.range i0 = LinearMap.ker p0 := by
    apply le_antisymm
    · rintro _ ⟨⟨v, w⟩, rfl⟩
      rw [LinearMap.mem_ker]
      exact Prod.ext v.2 w.2
    · rintro ⟨v, w⟩ hvw
      rw [LinearMap.mem_ker] at hvw
      exact ⟨(⟨v, congrArg Prod.fst hvw⟩, ⟨w, congrArg Prod.snd hvw⟩), rfl⟩
  have hex1 : LinearMap.range i1 = LinearMap.ker p1 := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact w.2
    · intro w hw
      exact ⟨⟨w, hw⟩, rfl⟩
  have hE : LinearMap.ker E.cechDiff = ⊥ :=
    ker_cechDiff_twistSections_eq_bot D.m D.a D.one_le_a
  exact Snake.finite_ker D.kerSections.cechDiff E.cechDiff S.cechDiff
    i0 i1 p0 p1 hi hp hi1 hp0 hex0 hex1 hE

end SerreData

end SerreH0

end TwoChartCech

@[expose] public section

namespace TwoChartCech.Sections

/-- **Finiteness of `H⁰` for a two-chart cover.** Let `R` be Noetherian and let
`f : A0`, `g : A1` restrict to mutually inverse elements of `A01`. If the chart modules
are finite over `R[f]` and `R[g]`, every overlap section becomes a restriction from either
chart after multiplying by a power of `ρ0 f`, resp. `ρ1 g`, and the kernels of `r0`, `r1`
are `f`-, resp. `g`-power torsion, then the Čech `H⁰` is a finite `R`-module. -/
public theorem finite_H0_of_chartFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {𝒰 : Cover.{u, v} R}
    (S : Sections.{u, v, w} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 := by
  obtain ⟨D⟩ := SerreH0.exists_serreData hfg hfin0 hfin1 hloc0 hloc1
  exact D.finite_H0 htors0 htors1

end TwoChartCech.Sections

end
