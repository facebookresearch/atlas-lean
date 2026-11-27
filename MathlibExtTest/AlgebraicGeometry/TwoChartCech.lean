/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.TwoChartCech
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

universe u

private theorem exactSource
    {R : Type u} [CommRing R] [IsNoetherianRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}
    (S : TwoChartCech.Sections.{u, u, u} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 :=
  TwoChartCech.Sections.finite_H0_of_chartFinite S f g hfg hfin0 hfin1 hloc0 hloc1
    htors0 htors1

/-- Higher-universe consumer: the cover algebras and the section modules may live in
universes different from the base ring. -/
example {R : Type u} [CommRing R] [IsNoetherianRing R]
    {𝒰 : TwoChartCech.Cover.{u, u + 1} R} (S : TwoChartCech.Sections.{u, u + 1, u + 2} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 :=
  TwoChartCech.Sections.finite_H0_of_chartFinite S f g hfg hfin0 hfin1 hloc0 hloc1
    htors0 htors1

/-- The cover of `Spec ℤ` by two copies of itself. -/
@[reducible] private noncomputable def trivialCover : TwoChartCech.Cover.{0, 0} ℤ where
  A0 := ℤ
  A1 := ℤ
  A01 := ℤ
  ρ0 := AlgHom.id ℤ ℤ
  ρ1 := AlgHom.id ℤ ℤ

/-- The structure sheaf on `trivialCover`. -/
@[reducible] private noncomputable def trivialSections : TwoChartCech.Sections.{0, 0, 0} trivialCover where
  M0 := ℤ
  M1 := ℤ
  M01 := ℤ
  M0_moduleA := (inferInstance : Module ℤ ℤ)
  M0_tower := (inferInstance : IsScalarTower ℤ ℤ ℤ)
  M1_moduleA := (inferInstance : Module ℤ ℤ)
  M1_tower := (inferInstance : IsScalarTower ℤ ℤ ℤ)
  M01_moduleA := (inferInstance : Module ℤ ℤ)
  M01_tower := (inferInstance : IsScalarTower ℤ ℤ ℤ)
  r0 := LinearMap.id
  r1 := LinearMap.id
  r0_smul _ _ := rfl
  r1_smul _ _ := rfl

/-- Every hypothesis holds on the trivial cover with `f = g = 1`, and `H⁰` is the
diagonal of `ℤ × ℤ`. -/
example : Module.Finite ℤ trivialSections.H0 := by
  refine TwoChartCech.Sections.finite_H0_of_chartFinite trivialSections
    (1 : trivialCover.A0) (1 : trivialCover.A1) (by simp)
    (Module.Finite.of_restrictScalars_finite ℤ _ _)
    (Module.Finite.of_restrictScalars_finite ℤ _ _) ?_ ?_ ?_ ?_
  · exact fun m => ⟨0, m, by rw [pow_zero, one_smul]; rfl⟩
  · exact fun m => ⟨0, m, by rw [pow_zero, one_smul]; rfl⟩
  · exact fun x hx => ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  · exact fun y hy => ⟨0, by rw [pow_zero, one_smul]; exact hy⟩

example (s : ℤ × ℤ) : s ∈ trivialSections.H0 ↔ s.1 = s.2 :=
  trivialSections.mem_H0_iff s
