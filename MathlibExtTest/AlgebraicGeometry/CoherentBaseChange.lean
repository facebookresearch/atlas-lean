/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from
https://github.com/anthropics/fermats-last-theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:

`Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean`: the four examples of
its `Gates` section (lines 105–119), and the statements of `Mumford.surjective_coprod`
and `Mumford.mem_K0_iff` (lines 73 and 83), restated by consumers below;
`Definitions/Def_AlgebraicGeometry_CoherentBaseChange.lean`: the statement of
`kerBaseChangeHom_apply_coe` (lines 67–69), restated by a consumer below;
`Definitions/Def_AlgebraicGeometry_CoherentBaseChangeFamily.lean`: the gluing
condition `hglue` (lines 20–21), restated by a consumer below.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
No individual authors are identified for these files in the upstream ATTRIBUTION.md.
-/

module

public import MathlibExt.AlgebraicGeometry.CoherentBaseChange
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CoherentBaseChange TwoChartCech
open scoped TensorProduct

universe u v w

-- Consumer with the original binders: the base-change comparison map
-- for a two-term complex of finite free modules.
example {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)
    (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker G.d)) :
    (G.kerBaseChangeHom A x : A ⊗[R] G.C0) =
      (LinearMap.ker G.d).subtype.baseChange A x :=
  LinearMap.tensorKer_coe A A G.d x

-- The comparison map is Mathlib's `LinearMap.tensorKer`, not a second construction.
example {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)
    (A : Type w) [CommRing A] [Algebra R A] :
    G.kerBaseChangeHom A = LinearMap.tensorKer A A G.d :=
  rfl

-- Higher-universe consumer for Mumford's truncation: membership is
-- `LinearMap.mem_ker` with `LinearMap.coprod_apply`.
example {R : Type u} [CommRing R] {C0 : Type v} {C1 : Type w}
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (z : C0 × (Fin (Mumford.rank d) → R)) :
    (z ∈ Mumford.K0 d ↔ d z.1 + Mumford.lift d z.2 = 0) := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

-- The examples of the source's `Gates` section (see the header).
-- Mumford's square commutes, with the original `Type u` binder.
example (R : Type u) [CommRing R] :
    (0 : R →ₗ[R] R) ∘ₗ Mumford.ι0 (0 : R →ₗ[R] R) =
      (-Mumford.lift (0 : R →ₗ[R] R)) ∘ₗ Mumford.dK (0 : R →ₗ[R] R) :=
  Mumford.comm 0

-- The two-chart kernel at the zero map: membership is a condition only
-- on the lift.
example (x : ℤ) (v : Fin (Mumford.rank (0 : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (x, v) ∈ Mumford.K0 (0 : ℤ →ₗ[ℤ] ℤ) ↔
      Mumford.lift (0 : ℤ →ₗ[ℤ] ℤ) v = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.zero_apply, zero_add]

example (v : Fin (Mumford.rank (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (-(Mumford.lift (LinearMap.id : ℤ →ₗ[ℤ] ℤ) v), v) ∈
      Mumford.K0 (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.id_apply, neg_add_cancel]

-- The generic two-chart kernel with a zero second map.
example {R : Type u} [CommRing R] (d : R →ₗ[R] R) (x : R) (p : PUnit) :
    (x, p) ∈ KerCoprod.K0 d (0 : PUnit →ₗ[R] R) ↔ d x = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.zero_apply, add_zero]

-- Surjectivity of the coproduct built from Mumford's lift.
example {R : Type u} [CommRing R] {C0 : Type v} {C1 : Type w}
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Function.Surjective (d.coprod (Mumford.lift d)) :=
  Mumford.surjective_coprod d

-- A fibre family over a scheme records the local fibre dimensions.
example {T : Scheme.{u}} (F : FibreH0Family.{u} T) (U : T.Opens)
    (hU : IsAffineOpen U) (t : U) :
    F.h0 t = (F.G U hU).fibreH0 (hU.primeIdealOf t) :=
  F.hglue U hU t

namespace CoherentBaseChangeTest

/-! ### Concrete complexes and points of `Spec ℤ` -/

/-- The complex `Rⁿ → Rᵐ` with zero differential. -/
private noncomputable abbrev zeroCx (R : Type u) [CommRing R] (n m : ℕ) :
    TwoTermComplex.{u, u} R where
  C0 := Fin n → R
  C1 := Fin m → R
  d := 0

/-- The complex `Rⁿ → Rⁿ` with identity differential. -/
private noncomputable abbrev idCx (R : Type u) [CommRing R] (n : ℕ) :
    TwoTermComplex.{u, u} R where
  C0 := Fin n → R
  C1 := Fin n → R
  d := LinearMap.id

/-- The complex `R → R` given by multiplication by `r`. -/
private noncomputable abbrev mulCx {R : Type u} [CommRing R] (r : R) :
    TwoTermComplex.{u, u} R where
  C0 := R
  C1 := R
  d := r • LinearMap.id

/-- The closed point `(2)` of `Spec ℤ`. -/
private noncomputable abbrev p2 : PrimeSpectrum ℤ :=
  ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two⟩

/-- The generic point `(0)` of `Spec ℤ`. -/
private noncomputable abbrev p0 : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩

/-! ### Fibre dimensions -/

/-- The Euler characteristic of the fibre at every prime is `chi` (rank-nullity over the
residue field). -/
private theorem fibreH0_sub_fibreH1 {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)
    (𝔭 : PrimeSpectrum R) : (G.fibreH0 𝔭 : ℤ) - G.fibreH1 𝔭 = G.chi := by
  have := 𝔭.nontrivial
  have h0 := LinearMap.finrank_range_add_finrank_ker
    (G.d.baseChange 𝔭.asIdeal.ResidueField)
  have h1 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (G.d.baseChange 𝔭.asIdeal.ResidueField))
  rw [Module.finrank_baseChange] at h0 h1
  rw [TwoTermComplex.fibreH0, TwoTermComplex.fibreH1, TwoTermComplex.chi]
  omega

/-- With zero differential, the fibre `H⁰` is the whole fibre of `C0`. -/
private theorem fibreH0_zeroCx {R : Type u} [CommRing R] (n m : ℕ)
    (𝔭 : PrimeSpectrum R) : (zeroCx R n m).fibreH0 𝔭 = n := by
  have := 𝔭.nontrivial
  rw [TwoTermComplex.fibreH0, LinearMap.baseChange_zero, LinearMap.ker_zero, finrank_top,
    Module.finrank_baseChange, Module.finrank_fin_fun]

/-- With zero differential, the fibre `H¹` is the whole fibre of `C1`. -/
private theorem fibreH1_zeroCx {R : Type u} [CommRing R] (n m : ℕ)
    (𝔭 : PrimeSpectrum R) : (zeroCx R n m).fibreH1 𝔭 = m := by
  have := 𝔭.nontrivial
  rw [TwoTermComplex.fibreH1, LinearMap.baseChange_zero, LinearMap.range_zero,
    (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, Module.finrank_baseChange,
    Module.finrank_fin_fun]

/-- With identity differential, both fibre cohomologies vanish. -/
private theorem fibreH0_idCx {R : Type u} [CommRing R] (n : ℕ) (𝔭 : PrimeSpectrum R) :
    (idCx R n).fibreH0 𝔭 = 0 := by
  rw [TwoTermComplex.fibreH0, LinearMap.baseChange_id, LinearMap.ker_id, finrank_bot]

private theorem fibreH1_idCx {R : Type u} [CommRing R] (n : ℕ) (𝔭 : PrimeSpectrum R) :
    (idCx R n).fibreH1 𝔭 = 0 := by
  have h := Submodule.finrank_quotient_add_finrank
    (⊤ : Submodule 𝔭.asIdeal.ResidueField
      (𝔭.asIdeal.ResidueField ⊗[R] (idCx R n).C1))
  rw [finrank_top] at h
  rw [TwoTermComplex.fibreH1, LinearMap.baseChange_id, LinearMap.range_id]
  omega

-- The zero complex `ℤ² → ℤ`: `H⁰` and `H¹` of every fibre have dimensions `2` and
-- `1`, and `χ = 1`.
example (𝔭 : PrimeSpectrum ℤ) :
    (zeroCx ℤ 2 1).fibreH0 𝔭 = 2 ∧ (zeroCx ℤ 2 1).fibreH1 𝔭 = 1 ∧
      (zeroCx ℤ 2 1).chi = 1 := by
  refine ⟨fibreH0_zeroCx 2 1 𝔭, fibreH1_zeroCx 2 1 𝔭, ?_⟩
  rw [TwoTermComplex.chi, Module.finrank_fin_fun, Module.finrank_fin_fun]
  norm_num

-- The identity complex `ℤ → ℤ`: every fibre is acyclic and `χ = 0`.
example (𝔭 : PrimeSpectrum ℤ) :
    (idCx ℤ 1).fibreH0 𝔭 = 0 ∧ (idCx ℤ 1).fibreH1 𝔭 = 0 ∧ (idCx ℤ 1).chi = 0 := by
  refine ⟨fibreH0_idCx 1 𝔭, fibreH1_idCx 1 𝔭, ?_⟩
  rw [TwoTermComplex.chi, sub_self]

/-- Base change of multiplication by `r` is multiplication by the image of `r`. -/
private theorem baseChange_mulCx_apply {R : Type u} [CommRing R] (r : R) (A : Type v)
    [CommRing A] [Algebra R A] (y : A ⊗[R] R) :
    (mulCx r).d.baseChange A y = algebraMap R A r • y := by
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply,
    LinearMap.id_apply, algebraMap_smul]

/-- At a prime containing `r`, the fibre of multiplication by `r` has `H⁰ = H¹ = κ(𝔭)`. -/
private theorem fibre_mulCx_of_mem {R : Type u} [CommRing R] (r : R) (𝔭 : PrimeSpectrum R)
    (hr : r ∈ 𝔭.asIdeal) : (mulCx r).fibreH0 𝔭 = 1 ∧ (mulCx r).fibreH1 𝔭 = 1 := by
  have := 𝔭.nontrivial
  have hd : (mulCx r).d.baseChange 𝔭.asIdeal.ResidueField = 0 := LinearMap.ext fun y => by
    rw [baseChange_mulCx_apply, Ideal.algebraMap_residueField_eq_zero.mpr hr, zero_smul,
      LinearMap.zero_apply]
  constructor
  · rw [TwoTermComplex.fibreH0, hd, LinearMap.ker_zero, finrank_top, Module.finrank_baseChange,
      Module.finrank_self]
  · rw [TwoTermComplex.fibreH1, hd, LinearMap.range_zero,
      (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq, Module.finrank_baseChange,
      Module.finrank_self]

/-- At a prime not containing `r`, the fibre of multiplication by `r` is acyclic. -/
private theorem fibre_mulCx_of_notMem {R : Type u} [CommRing R] (r : R) (𝔭 : PrimeSpectrum R)
    (hr : r ∉ 𝔭.asIdeal) : (mulCx r).fibreH0 𝔭 = 0 ∧ (mulCx r).fibreH1 𝔭 = 0 := by
  have hker : LinearMap.ker ((mulCx r).d.baseChange 𝔭.asIdeal.ResidueField) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun y hy => by
      rw [baseChange_mulCx_apply] at hy
      exact (smul_eq_zero.mp hy).resolve_left (mt Ideal.algebraMap_residueField_eq_zero.mp hr)
  have h0 : (mulCx r).fibreH0 𝔭 = 0 := by rw [TwoTermComplex.fibreH0, hker, finrank_bot]
  have hchi : (mulCx r).chi = 0 := by rw [TwoTermComplex.chi, sub_self]
  have h := fibreH0_sub_fibreH1 (mulCx r) 𝔭
  rw [h0, hchi] at h
  exact ⟨h0, by omega⟩

-- Multiplication by `2` on `ℤ`: `χ = 0`, the fibre over `(2)` has `H⁰` and `H¹` of
-- dimension `1`, and the generic fibre is acyclic.
example :
    (mulCx (2 : ℤ)).chi = 0 ∧
      (mulCx (2 : ℤ)).fibreH0 p2 = 1 ∧ (mulCx (2 : ℤ)).fibreH1 p2 = 1 ∧
      (mulCx (2 : ℤ)).fibreH0 p0 = 0 ∧ (mulCx (2 : ℤ)).fibreH1 p0 = 0 := by
  obtain ⟨h0, h1⟩ := fibre_mulCx_of_mem 2 p2 (Ideal.mem_span_singleton_self 2)
  obtain ⟨g0, g1⟩ := fibre_mulCx_of_notMem 2 p0 (by simp)
  exact ⟨by rw [TwoTermComplex.chi, sub_self], h0, h1, g0, g1⟩

-- Every scheme carries the fibre family of the zero complex `𝒪ⁿ → 0` on its
-- affine opens: its fibre `H⁰` has dimension `n` at every point.
example (T : Scheme.{u}) (n : ℕ) : ∃ F : FibreH0Family.{u} T, ∀ t, F.h0 t = n :=
  ⟨{ G := fun U _ => zeroCx Γ(T, U) n 0
     h0 := fun _ => n
     hglue := fun _ hU t => (fibreH0_zeroCx n 0 (hU.primeIdealOf t)).symm }, fun _ => rfl⟩

/-! ### The base-change comparison map -/

-- Along `ℤ → ℚ` the comparison map of the zero complex sends `q ⊗ v` to `q ⊗ v`.
example (q : ℚ) (v : Fin 2 → ℤ) :
    ((zeroCx ℤ 2 1).kerBaseChangeHom ℚ (q ⊗ₜ ⟨v, LinearMap.mem_ker.mpr rfl⟩) :
      ℚ ⊗[ℤ] (Fin 2 → ℤ)) = q ⊗ₜ v :=
  LinearMap.tensorKer_tmul ℚ ℚ (zeroCx ℤ 2 1).d q _

-- For the zero complex the comparison map is surjective along `ℤ → 𝔽₂`.
example : Function.Surjective ((zeroCx ℤ 2 1).kerBaseChangeHom (ZMod 2)) := by
  rintro ⟨y, -⟩
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (ZMod 2)
    (g := (LinearMap.ker (zeroCx ℤ 2 1).d).subtype)
    (fun v => ⟨⟨v, LinearMap.mem_ker.mpr rfl⟩, rfl⟩) y
  exact ⟨x, Subtype.ext (LinearMap.tensorKer_coe (ZMod 2) (ZMod 2) _ x)⟩

-- `H⁰` does not commute with the base change `ℤ → 𝔽₂` for multiplication by `2`:
-- `ker 2 = 0` over `ℤ`, while `1 ⊗ 1` is a nonzero element of `H⁰` over `𝔽₂`.
example : ¬ Function.Surjective ((mulCx (2 : ℤ)).kerBaseChangeHom (ZMod 2)) := by
  have hker (m : LinearMap.ker (mulCx (2 : ℤ)).d) : m = 0 := by
    obtain ⟨m, hm⟩ := m
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_zero] at hm
    exact Subtype.ext (hm.resolve_left two_ne_zero)
  have hzero (x : ZMod 2 ⊗[ℤ] LinearMap.ker (mulCx (2 : ℤ)).d) :
      (mulCx (2 : ℤ)).kerBaseChangeHom (ZMod 2) x = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => rw [hker m, TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have hmem : (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) ∈ (mulCx (2 : ℤ)).H0 (ZMod 2) := by
    rw [TwoTermComplex.H0, LinearMap.mem_ker, baseChange_mulCx_apply,
      show algebraMap ℤ (ZMod 2) 2 = 0 by rw [map_ofNat]; decide, zero_smul]
  have hne : (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) ≠ 0 := by
    intro h
    have h' := congrArg (TensorProduct.rid ℤ (ZMod 2)) h
    rw [TensorProduct.rid_tmul, map_zero, one_smul] at h'
    exact one_ne_zero h'
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ⟨_, hmem⟩
  rw [hzero] at hx
  exact hne (congrArg Subtype.val hx).symm

end CoherentBaseChangeTest
