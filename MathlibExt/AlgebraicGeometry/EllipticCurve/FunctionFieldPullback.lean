/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_EllipticCurve_FunctionFieldPullback.lean`,
`Theorems/Thm_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean`
and the proof files
`P2M/Sol/S_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top.lean`,
`P2M/Sol/S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq.lean`,
`P2M/Sol/S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top.lean`,
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_zsmul_genericPoint_good.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

import MathlibExt.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
import MathlibExt.AlgebraicGeometry.EllipticCurve.DivisionPolynomialZSMul
import MathlibExt.AlgebraicGeometry.EllipticCurve.XYIdeal
import MathlibExt.AlgebraicGeometry.EllipticCurve.TorsionCardinality

@[expose] public noncomputable section

/-!
# Function-field pullbacks on a Weierstrass curve

For a Weierstrass curve `W` over `F` and a field `K` over `F`, this file works in the function
field of `W⁄K`. It defines the generic point `genericPoint W K`, the pullback of functions along
translation by a point (`transEquiv W K S`, an algebra automorphism), the pullback along
multiplication by an integer `n` (`mulPull W K n h`), and the place `placeOf W K P hP` of a nonzero
point `P`, that is, of a nonsingular affine point. `mulPull W K n h` takes a proof
`h : MulGood W K n` that `n • genericPoint W K` is nonzero and is not the base change of a point
over `K`; when `K` is algebraically closed, `W` is elliptic and `(n : K) ≠ 0`,
`zsmul_genericPoint_good` provides it.

Valuations at places are those of `IsDedekindDomain.HeightOneSpectrum.valuation`: a value below
`1` means that the function vanishes there, so `WithZero.exp (-1)` is a simple zero and
`WithZero.exp 1` is a simple pole.

## Main results

* `WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq`: let `g` be a function that is fixed
  by translation by every `n`-torsion point and that, at every affine point `P` with `n • P ≠ 0`,
  has a simple zero when `n • P = T` and valuation `1` otherwise. Then `T = 0`.
* `WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq_of_pole`: the same with a simple pole
  in place of the simple zero.
* `WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le`: the function field has degree at most
  `n.natAbs ^ 2` over the image of `mulPull W K n h`.
* `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed`: over an algebraically closed
  field, every point is divisible by every nonzero integer.

The two nondegeneracy results assume that `W` is elliptic, that `K` is algebraically closed with
`(n : K) ≠ 0`, that the coordinate ring of `W⁄K` is a Dedekind domain, and, as the hypothesis
`hpull`, that for every natural number `k` and every affine point `P` with `n • P ≠ 0`, the
pullback along `mulPull` of a function that vanishes to order at least `k` at `n • P` (valuation
at most `exp (-k)` there) vanishes to order at least `k` at `P`. Since `k` is a natural number,
`hpull` constrains only vanishing orders `k ≥ 0`.
-/


set_option autoImplicit false

open scoped WeierstrassCurve.Affine

namespace FunctionFieldPullback.FinrankPair

open Polynomial IntermediateField

namespace WeilPairingDEGN

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private lemma algHom_ext_of_adjoin_eq_top {L' : Type*} [Field L'] [Algebra K L'] {S : Set L}
    (hS : adjoin K S = ⊤) {f g : L →ₐ[K] L'} (h : ∀ s ∈ S, f s = g s) : f = g := by
  have hle : adjoin K S ≤ (⊤ : IntermediateField K L) := le_top
  have key : (adjoin K S).toSubfield ≤ (f : L →+* L').eqLocusField (g : L →+* L') := by
    change Subfield.closure (Set.range (algebraMap K L) ∪ S) ≤ _
    rw [Subfield.closure_le]
    rintro x (⟨k, rfl⟩ | hx)
    · simp
    · exact h x hx
  ext z
  have hz : z ∈ (adjoin K S).toSubfield := by rw [hS]; trivial
  exact key hz

private lemma eq_top_of_forall_mem {B : Type*} [Field B] [Algebra K B] [Algebra B L]
    [IsScalarTower K B L]
    {S : Set L} (hS : adjoin K S = ⊤) (N : IntermediateField B L) (h : ∀ s ∈ S, s ∈ N) : N = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top, eq_top_iff, ← hS, adjoin_le_iff]
  exact h

private theorem finrank_fieldRange_le (X Y : L) (hgen : adjoin K {X, Y} = ⊤) (A B : L)
    (hA : A ∈ K⟮X⟯) (hB : B ∈ K⟮X⟯) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L)
    (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : K[X])
    {d : ℕ} (hd : 0 < d) (hroot : aeval X Φ = μ X * aeval X Ψ)
    (hdeg : ∀ (M : IntermediateField K L) (c : M),
      (Φ.map (algebraMap K M) - C c * Ψ.map (algebraMap K M)).natDegree = d) :
    FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d := by
  set M : IntermediateField K L := μ.fieldRange with hM
  have hxM : μ X ∈ M := ⟨X, rfl⟩
  have hyM : μ Y ∈ M := ⟨Y, rfl⟩
  set P : M[X] := Φ.map (algebraMap K M) - C (⟨μ X, hxM⟩ : M) * Ψ.map (algebraMap K M) with hP
  have hPdeg : P.natDegree = d := hdeg M _
  have hP0 : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hPdeg; omega
  have hPX : aeval X P = 0 := by
    rw [hP, map_sub, map_mul, aeval_map_algebraMap, aeval_map_algebraMap, aeval_C, hroot]
    change μ X * aeval X Ψ - (algebraMap M L ⟨μ X, hxM⟩) * aeval X Ψ = 0
    rw [sub_eq_zero]; rfl
  have hXalg : IsAlgebraic M X := ⟨P, hP0, hPX⟩
  have hXint : IsIntegral M X := hXalg.isIntegral
  have hN'fd : FiniteDimensional M M⟮X⟯ := adjoin.finiteDimensional hXint
  have hN'deg : Module.finrank M M⟮X⟯ ≤ d := by
    rw [adjoin.finrank hXint, ← hPdeg]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero M X hP0 hPX)
  have hKX : K⟮X⟯ ≤ (M⟮X⟯).restrictScalars K := by
    rw [adjoin_simple_le_iff]
    exact mem_adjoin_simple_self M X
  have hAN : A ∈ M⟮X⟯ := hKX hA
  have hBN : B ∈ M⟮X⟯ := hKX hB
  have hMN : ∀ z : L, z ∈ M → z ∈ M⟮X⟯ := fun z hz => (M⟮X⟯).algebraMap_mem ⟨z, hz⟩
  have hpair : ∀ {P : L → Prop}, P X → P Y → ∀ s ∈ ({X, Y} : Set L), P s := by
    intro P hX hY s hs
    rcases hs with h | h
    · rw [h]; exact hX
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact hY
  have hXY : ∀ N : IntermediateField K L, X ∈ N → Y ∈ N → N = ⊤ := fun N hX hY =>
    eq_top_of_forall_mem hgen N (hpair hX hY)
  set N : IntermediateField K L := (M⟮X⟯).restrictScalars K with hN
  have hmemN : ∀ z, z ∈ N ↔ z ∈ M⟮X⟯ := fun z => IntermediateField.mem_restrictScalars K
  have hXN : X ∈ N := (hmemN X).mpr (mem_adjoin_simple_self M X)
  have hYN : Y ∈ N := by
    by_contra hYN
    set a : N := ⟨A, (hmemN A).mpr hAN⟩ with ha
    set b : N := ⟨B, (hmemN B).mpr hBN⟩ with hb
    set q : N[X] := Polynomial.X ^ 2 + (C a * Polynomial.X + C b) with hq
    have hlow : (C a * Polynomial.X + C b).degree < 2 := by
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast Nat.lt_succ_self 1)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
    have hqm : q.Monic := monic_X_pow_add hlow
    have hqdeg : q.natDegree = 2 := by
      rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
      rwa [degree_X_pow]
    have hq0 : q ≠ 0 := hqm.ne_zero
    have haeval : ∀ z : L, aeval z q = z ^ 2 + A * z + B := by
      intro z
      rw [hq]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
      rw [add_assoc]
      rfl
    have hqY : aeval Y q = 0 := by rw [haeval, hY]
    have hYint : IsIntegral N Y := ⟨q, hqm, by rwa [← aeval_def]⟩
    have hmin2 : 2 ≤ (minpoly N Y).natDegree := by
      rw [minpoly.two_le_natDegree_iff hYint]
      rintro ⟨z, hz⟩
      exact hYN (hz ▸ z.2)
    have hmin : minpoly N Y = q := by
      symm
      apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hYint) hqm
        (minpoly.dvd N Y hqY)
      rw [hqdeg]; exact hmin2
    have hιroot : ι Y ∈ (minpoly N Y).aroots L := by
      rw [mem_aroots', hmin]
      exact ⟨Polynomial.map_ne_zero hq0, by rw [haeval, hιY]⟩
    have hXNY : X ∈ N⟮Y⟯ := (N⟮Y⟯).algebraMap_mem ⟨X, hXN⟩
    have hYNY : Y ∈ N⟮Y⟯ := mem_adjoin_simple_self N Y
    have htop : N⟮Y⟯ = ⊤ := eq_top_of_forall_mem hgen _ (hpair hXNY hYNY)
    let e : L ≃ₐ[N] N⟮Y⟯ :=
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm
    let θ₀ : N⟮Y⟯ →ₐ[N] L := (algHomAdjoinIntegralEquiv N hYint).symm ⟨ι Y, hιroot⟩
    let θ : L →ₐ[N] L := θ₀.comp e
    have heY : e Y = AdjoinSimple.gen N Y := by
      apply Subtype.ext; rfl
    have hθY : θ Y = ι Y := by
      change θ₀ (e Y) = ι Y
      rw [heY]
      exact algHomAdjoinIntegralEquiv_symm_apply_gen N hYint ⟨ι Y, hιroot⟩
    have hθfix : ∀ z : L, z ∈ N → θ z = z := fun z hz => θ.commutes ⟨z, hz⟩
    have hθX : θ.restrictScalars K X = ι X := by
      rw [AlgHom.restrictScalars_apply, hθfix _ hXN, hιX]
    have hθY' : θ.restrictScalars K Y = ι Y := by
      rw [AlgHom.restrictScalars_apply, hθY]
    have hθι : θ.restrictScalars K = ι :=
      algHom_ext_of_adjoin_eq_top hgen (hpair (P := fun s => θ.restrictScalars K s = ι s) hθX hθY')
    apply hιμ
    rw [← hθι, AlgHom.restrictScalars_apply]
    exact hθfix _ ((hmemN _).mpr (hMN _ hyM))
  have htop' : M⟮X⟯ = ⊤ :=
    eq_top_of_forall_mem hgen (M⟮X⟯) (hpair (mem_adjoin_simple_self M X) ((hmemN Y).mp hYN))
  let e' : M⟮X⟯ ≃ₐ[M] L := (IntermediateField.equivOfEq htop').trans IntermediateField.topEquiv
  refine ⟨LinearEquiv.finiteDimensional e'.toLinearEquiv, ?_⟩
  rw [← LinearEquiv.finrank_eq e'.toLinearEquiv]
  exact hN'deg

end WeilPairingDEGN

private theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] (X Y : L)
    (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L)
    (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X})
    (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0)
    (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ} (hd : 0 < d)
    (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ)
    (hdeg : ∀ (M : IntermediateField K L) (c : M),
      (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d)
    : FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d :=
  WeilPairingDEGN.finrank_fieldRange_le X Y hgen A B hA hB hY μ ι hιX hιY hιμ Φ Ψ hd hroot hdeg
end FunctionFieldPullback.FinrankPair


/-- **Degree of a field over the image of an endomorphism.** Let `L` be a field extension of `K`
generated by `X` and `Y`, where `Y ^ 2 + A * Y + B = 0` with `A` and `B` in `K⟮X⟯`. Let `μ` and
`ι` be `K`-endomorphisms of `L` such that `ι` fixes `X`, sends `Y` to a root of the same quadratic
and moves `μ Y`. Let `Φ` and `Ψ` be fixed polynomials with coefficients in `K` such that
`Φ(X) = μ(X) * Ψ(X)`, and let `d > 0`. Suppose that for every intermediate field `K ⊆ M ⊆ L` and
every `c ∈ M`, the polynomial `Φ - c * Ψ`, with the coefficients of `Φ` and `Ψ` mapped into `M`,
has degree `d`. Then `L` is finite over the image of `μ`, of degree at most `d`. -/
theorem IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top {K L : Type*} [Field K]
    [Field L] [Algebra K L] (X Y : L) (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L)
    (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X})
    (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X)
    (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ}
    (hd : 0 < d) (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ)
    (hdeg : ∀ (M : IntermediateField K L) (c : M),
      (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d) :
    FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d :=
  FunctionFieldPullback.FinrankPair.solution X Y hgen A B hA hB hY μ ι hιX hιY hιμ Φ Ψ hd hroot hdeg


open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [Field K] {W : Affine K}

instance moduleFinite : Module.Finite K[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

theorem algebraMap_eq_mk_C (p : K[X]) : algebraMap K[X] W.CoordinateRing p = mk W (C p) := rfl

theorem isMaximal_of_isPrime {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    P.IsMaximal := by
  have hc : (P.comap (algebraMap K[X] W.CoordinateRing)) ≠ ⊥ := fun h =>
    hP (Ideal.eq_bot_of_under_eq_bot h)
  have : (P.comap (algebraMap K[X] W.CoordinateRing)).IsMaximal :=
    IsPrime.to_maximal_ideal hc
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K[X]) P inferInstance

theorem exists_comap_eq_span [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥)
    [P.IsPrime] :
    ∃ a : K, P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a} := by
  set p := P.comap (algebraMap K[X] W.CoordinateRing) with hp
  have hp0 : p ≠ ⊥ := fun h => hP (Ideal.eq_bot_of_under_eq_bot h)
  have : p.IsPrime := Ideal.comap_isPrime _ P
  have hpmax : p.IsMaximal := IsPrime.to_maximal_ideal hp0
  set g := Submodule.IsPrincipal.generator p with hg
  have hgp : Ideal.span {g} = p := Ideal.span_singleton_generator p
  have hgprime : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime p hp0
  have hdeg : g.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K hgprime.irreducible
  obtain ⟨a, ha⟩ := Polynomial.exists_root_of_degree_eq_one hdeg
  refine ⟨a, ?_⟩
  have hle : p ≤ Ideal.span {X - C a} := by
    rw [← hgp, Ideal.span_singleton_le_span_singleton]
    exact ⟨g /ₘ (X - C a), (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm⟩
  exact (hpmax.eq_of_le (Ideal.span_singleton_ne_top (Polynomial.not_isUnit_X_sub_C a)) hle).symm
    |>.symm

theorem XClass_mem_of_comap_eq {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) : XClass W a ∈ P := by
  have : X - C a ∈ P.comap (algebraMap K[X] W.CoordinateRing) := by
    rw [h]; exact Ideal.mem_span_singleton_self _
  exact this

theorem mk_C_mem_iff {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) (q : K[X]) :
    mk W (C q) ∈ P ↔ q.IsRoot a := by
  change q ∈ P.comap (algebraMap K[X] W.CoordinateRing) ↔ _
  rw [h, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]

theorem XYIdeal_isMaximal {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField K)
    (quotientXYIdealEquiv (W' := W) (x := a) (y := C b) h).toMulEquiv

theorem algebraMap_quot_apply (P : Ideal W.CoordinateRing) (c : K) :
    algebraMap K (W.CoordinateRing ⧸ P) c = Ideal.Quotient.mk P (mk W (C (C c))) := rfl

theorem algebraMap_quot_eq_comp_eval {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) :
    algebraMap K[X] (W.CoordinateRing ⧸ P) =
      (algebraMap K (W.CoordinateRing ⧸ P)).comp (evalRingHom a) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X]
    rw
        [algebraMap_quot_apply, IsScalarTower.algebraMap_apply K[X] W.CoordinateRing
          (W.CoordinateRing ⧸ P),
      Ideal.Quotient.algebraMap_eq, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have : mk W (C (C a)) - algebraMap K[X] W.CoordinateRing X = -XClass W a := by
      simp only [algebraMap_eq_mk_C, XClass, map_sub]; abel
    rw [this]
    exact P.neg_mem (XClass_mem_of_comap_eq h)

theorem exists_eq_XYIdeal [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by
  obtain ⟨a, ha⟩ := exists_comap_eq_span hP
  have hPmax : P.IsMaximal := isMaximal_of_isPrime hP
  set L := W.CoordinateRing ⧸ P
  set π := Ideal.Quotient.mk P
  have hθ := algebraMap_quot_eq_comp_eval ha
  have : Algebra.IsIntegral K L := ⟨fun z => by
    obtain ⟨m, hm, hm0⟩ := Algebra.IsIntegral.isIntegral (R := K[X]) z
    refine ⟨m.map (evalRingHom a), hm.map _, ?_⟩
    rw [eval₂_map, ← hθ]
    exact hm0⟩
  obtain ⟨b, hb⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := L)).2
      (π (mk W Y))
  have hYmem : YClass W (C b) ∈ P := by
    rw [YClass, map_sub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hb.symm
  have heq : W.Equation a b := by
    have hψ : π.comp (mk W) = (algebraMap K L).comp (evalEvalRingHom a b) := by
      apply Polynomial.ringHom_ext
      · intro q
        change algebraMap K[X] L q = _
        rw [hθ]
        simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X, eval_C]
        exact hb.symm
    have h0 : (π.comp (mk W)) W.polynomial = 0 := by
      rw [RingHom.comp_apply, AdjoinRoot.mk_self, map_zero]
    rw [hψ, RingHom.comp_apply, coe_evalEvalRingHom, map_eq_zero] at h0
    exact h0
  refine ⟨a, b, heq, ?_⟩
  have hle : XYIdeal W a (C b) ≤ P := by
    rw [XYIdeal, Ideal.span_le]
    rintro z (rfl | rfl)
    · exact XClass_mem_of_comap_eq ha
    · exact hYmem
  exact ((XYIdeal_isMaximal heq).eq_of_le hPmax.ne_top hle).symm

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

namespace Point

variable {S : Type*} [CommRing S] {V : Affine S}

/-- **`x`-coordinate of a point.** For a Weierstrass curve `V` over a commutative ring, a point
of `V` is the point at infinity or a nonsingular affine point `(x, y)`; this is `x` at `(x, y)`
and `0` at the point at infinity. Over a field it agrees with
`WeierstrassCurve.Affine.Point.xCoordOrZero`, which is stated only for curves over a field. -/
def xc : V.Point → S
  | 0 => 0
  | some x _ _ => x

/-- **`y`-coordinate of a point.** For a Weierstrass curve `V` over a commutative ring, a point
of `V` is the point at infinity or a nonsingular affine point `(x, y)`; this is `y` at `(x, y)`
and `0` at the point at infinity. -/
def yc : V.Point → S
  | 0 => 0
  | some _ y _ => y

@[simp] lemma xc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).xc = x := rfl
@[simp] lemma yc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).yc = y := rfl

lemma nonsingular_xc_yc {P : V.Point} (hP : P ≠ 0) : V.Nonsingular P.xc P.yc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

lemma eq_some_xc_yc {P : V.Point} (hP : P ≠ 0) : P = some P.xc P.yc (nonsingular_xc_yc hP) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

end Point

section Generic

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

/-- **Decidable equality on the function field.** Points over the function field are added with
this one classical instance, which takes precedence over Mathlib's `FractionRing.instDecidableEq`
wherever `WeierstrassCurve.Affine` is open (as the `W⁄K` notation requires), so that every
statement about such points uses the same group law. -/
noncomputable scoped instance instDecidableEqFunctionField : DecidableEq (W⁄K).FunctionField :=
  Classical.decEq _

/-- **Generic `x`.** The class of `X` in the function field of `W⁄K`. -/
noncomputable def genericX : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X))

/-- **Generic `y`.** The class of `Y` in the function field of `W⁄K`. -/
noncomputable def genericY : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) Y)

theorem evalEval_baseChange_polynomial (x y : (W⁄K).FunctionField) :
    (W⁄(W⁄K).FunctionField).polynomial.evalEval x y =
      (W⁄K).polynomial.eval₂ (aeval (R := K) x).toRingHom y := by
  rw [baseChange_polynomial W (Algebra.ofId K (W⁄K).FunctionField), evalEval, eval_map]
  have h := hom_eval₂ (W⁄K).polynomial (mapRingHom (Algebra.ofId K (W⁄K).FunctionField : K →+* _))
    (evalRingHom x) (C y)
  simp only [coe_evalRingHom, eval_C] at h
  rw [h]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, coe_evalRingHom,
      eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_evalRingHom,
      eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

theorem algebraMap_comp_of :
    (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField).comp (AdjoinRoot.of (W⁄K).polynomial) =
      (aeval (R := K) (genericX W K)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_C]
    rw [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change (algebraMap K[X] (W⁄K).FunctionField) (algebraMap K K[X] c) = _
    exact (IsScalarTower.algebraMap_apply K K[X] (W⁄K).FunctionField c).symm
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X]
    rfl

theorem generic_equation :
    (W⁄(W⁄K).FunctionField).Equation (genericX W K) (genericY W K) := by
  rw [Equation, evalEval_baseChange_polynomial, ← algebraMap_comp_of]
  have h0 := congrArg (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)
    (AdjoinRoot.eval₂_root (W⁄K).polynomial)
  rw [map_zero, hom_eval₂] at h0
  exact h0

theorem generic_nonsingular [W.IsElliptic] :
    (W⁄(W⁄K).FunctionField).Nonsingular (genericX W K) (genericY W K) := by
  have : (W⁄(W⁄K).FunctionField).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap R (W⁄K).FunctionField)).IsElliptic)
  exact (equation_iff_nonsingular (W := W⁄(W⁄K).FunctionField)).mp (generic_equation W K)

/-- **Generic point.** For an elliptic curve `W`, the point `(genericX W K, genericY W K)` of `W`
over the function field of `W⁄K`. -/
noncomputable def genericPoint [W.IsElliptic] : (W⁄(W⁄K).FunctionField).Point :=
  .some _ _ (generic_nonsingular W K)

end Generic

section PointHom

variable {R : Type*} [Field R] {W : WeierstrassCurve R} {K : Type*} [Field K] [Algebra R K]

theorem eval₂_polynomial_of_point (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).polynomial.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc = 0 := by
  rw [← evalEval_baseChange_polynomial]
  exact (Point.nonsingular_xc_yc hQ).left

/-- **Evaluation at a point over the function field.** For a nonzero point `Q` of `W` over the
function field of `W⁄K`, that is, a nonsingular affine point `(x, y)` with `x` and `y` in the
function field, the `K`-algebra map from the coordinate ring of `W⁄K` to the function field that
sends `X` to `x` and `Y` to `y`. -/
noncomputable def pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).CoordinateRing →ₐ[K] (W⁄K).FunctionField :=
  { AdjoinRoot.lift (aeval (R := K) Q.xc).toRingHom Q.yc (eval₂_polynomial_of_point Q hQ) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_ofClass]
      rw [IsScalarTower.algebraMap_apply K (Polynomial K) (W⁄K).CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.algebraMap_apply, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] }

theorem pointHom_mk (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : (Polynomial K)[X]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) = g.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_point Q hQ) g

@[simp] theorem pointHom_mk_C_C (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (c : K) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C (C c))) = algebraMap K _ c :=
  (pointHom Q hQ).commutes c

@[simp] theorem pointHom_mk_C_X (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C X)) = Q.xc := by
  rw [pointHom_mk, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

@[simp] theorem pointHom_mk_Y (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) Y) = Q.yc := by
  rw [pointHom_mk, eval₂_X]

theorem CoordinateRing.algHom_ext' {A : Type*} [Semiring A] [Algebra K A]
    {f g : (W⁄K).CoordinateRing →ₐ[K] A}
    (hX : f (CoordinateRing.mk (W⁄K) (C X)) = g (CoordinateRing.mk (W⁄K) (C X)))
    (hY : f (CoordinateRing.mk (W⁄K) Y) = g (CoordinateRing.mk (W⁄K) Y)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change f (CoordinateRing.mk (W⁄K) (C q)) = g (CoordinateRing.mk (W⁄K) (C q))
    have hf : (f : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) =
        (g : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K _ c) = g (algebraMap K _ c)
        rw [AlgHom.commutes, AlgHom.commutes]
      · exact hX
    exact RingHom.congr_fun hf q
  · exact hY

theorem pointHom_genericPoint [W.IsElliptic] :
    pointHom (genericPoint W K) (Point.some_ne_zero _) =
      IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField := by
  change pointHom (Point.some _ _ (generic_nonsingular W K)) _ =
      IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField
  apply CoordinateRing.algHom_ext'
  · rw [pointHom_mk_C_X, IsScalarTower.coe_toAlgHom', Point.xc_some]; rfl
  · rw [pointHom_mk_Y, IsScalarTower.coe_toAlgHom', Point.yc_some]; rfl

theorem Point.xc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).xc = f P.xc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

theorem Point.yc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).yc = f P.yc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

theorem pointHom_injective_of_ne_baseChange [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hQK : ∀ P : (W⁄K).Point, Q ≠ Point.baseChange K (W⁄K).FunctionField P) :
    Function.Injective (pointHom Q hQ) := by
  rw [injective_iff_map_eq_zero]
  by_contra hcon
  push Not at hcon
  have hker : RingHom.ker (pointHom Q hQ) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := hcon
    intro h
    have hm : a ∈ RingHom.ker (pointHom Q hQ) := (RingHom.mem_ker).mpr ha
    rw [h, Ideal.mem_bot] at hm
    exact ha0 hm
  have : (RingHom.ker (pointHom Q hQ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨a, b, hab, hker'⟩ := CoordinateRing.exists_eq_XYIdeal hker
  have : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hns : (W⁄K).Nonsingular a b := (equation_iff_nonsingular (W := W⁄K)).mp hab
  have hx : Q.xc = algebraMap K _ a := by
    have : CoordinateRing.XClass (W⁄K) a ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert _ _)
    rw [RingHom.mem_ker, CoordinateRing.XClass, map_sub, map_sub, map_sub, pointHom_mk_C_X,
      pointHom_mk_C_C, sub_eq_zero] at this
    exact this
  have hy : Q.yc = algebraMap K _ b := by
    have : CoordinateRing.YClass (W⁄K) (C b) ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    rw [RingHom.mem_ker, CoordinateRing.YClass, map_sub, map_sub, pointHom_mk_Y, pointHom_mk_C_C,
      sub_eq_zero] at this
    exact this
  apply hQK (.some a b hns)
  rw [Point.eq_some_xc_yc hQ, Point.baseChange, Point.map_some]
  congr 1

/-- **Pullback along a point over the function field.** For a nonzero point `Q` of `W` over the
function field of `W⁄K`, that is, a nonsingular affine point, such that `pointHom Q hQ` is
injective, the extension of `pointHom Q hQ` to a `K`-algebra endomorphism of the function field:
the pullback of functions along the map of curves that `Q` defines. -/
noncomputable def pointPull (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  IsFractionRing.liftAlgHom hinj

@[simp] theorem pointPull_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (h : (W⁄K).CoordinateRing) :
    pointPull Q hQ hinj (algebraMap _ _ h) = pointHom Q hQ h := by
  rw [pointPull, IsFractionRing.liftAlgHom_apply]
  exact IsFractionRing.lift_algebraMap hinj h

theorem map_pointPull_genericPoint [W.IsElliptic] (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    Point.map (pointPull Q hQ hinj) (genericPoint W K) = Q := by
  conv_rhs => rw [Point.eq_some_xc_yc hQ]
  rw [genericPoint, Point.map_some]
  congr 1
  · rw [genericX, pointPull_algebraMap, pointHom_mk_C_X]
  · rw [genericY, pointPull_algebraMap, pointHom_mk_Y]

theorem pointPull_comp_pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (pointPull Q hQ hinj) P ≠ 0) :
    (pointPull Q hQ hinj).comp (pointHom P hP) = pointHom (Point.map (pointPull Q hQ hinj) P) hP' :=
        by
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, Point.xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, Point.yc_map]

theorem pointHom_congr {Q Q' : (W⁄(W⁄K).FunctionField).Point} (h : Q = Q') (hQ : Q ≠ 0)
    (hQ' : Q' ≠ 0) :
    pointHom Q hQ = pointHom Q' hQ' := by subst h; rfl

theorem pointPull_comp_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) = pointHom Q hQ :=
  RingHom.ext fun h => pointPull_algebraMap Q hQ hinj h

theorem FunctionField.algHom_ext {φ ψ : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField}
    (h : (φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      (ψ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)) : φ = ψ :=
  AlgHom.toRingHom_injective
    (IsLocalization.ringHom_ext (nonZeroDivisors (W⁄K).CoordinateRing) h)

theorem exists_eq_baseChange_of_isIntegral_xc [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (hx : _root_.IsIntegral K Q.xc) :
    ∃ P : (W⁄K).Point, Q = Point.baseChange K (W⁄K).FunctionField P := by
  have : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hdx : (minpoly K Q.xc).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx)
  obtain ⟨a, ha⟩ : Q.xc ∈ (algebraMap K (W⁄K).FunctionField).range :=
      minpoly.mem_range_of_degree_eq_one K _ hdx
  have heq := (Point.nonsingular_xc_yc hQ).left
  rw [equation_iff] at heq
  have hy : _root_.IsIntegral K Q.yc := by
    refine
        ⟨X ^ 2 + C ((W⁄K).a₁ * a + (W⁄K).a₃) * X - C
          (a ^ 3 + (W⁄K).a₂ * a ^ 2 + (W⁄K).a₄ * a + (W⁄K).a₆),
      ?_, ?_⟩
    · have hlt : (C ((W⁄K).a₁ * a + (W⁄K).a₃) * X -
          C (a ^ 3 + (W⁄K).a₂ * a ^ 2 + (W⁄K).a₄ * a + (W⁄K).a₆) : K[X]).degree < ((X : K[X]) ^
              2).degree := by
        rw [degree_X_pow]
        refine (degree_sub_le _ _).trans_lt (max_lt ((degree_C_mul_X_le _).trans_lt ?_)
          (degree_C_le.trans_lt ?_))
        · exact WithBot.coe_lt_coe.mpr (by norm_num)
        · exact WithBot.coe_lt_coe.mpr (by norm_num)
      rw [add_sub_assoc]
      exact (monic_X_pow 2).add_of_left hlt
    · simp only
        [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, map_add, map_mul, map_pow]
      rw [ha]
      have e1 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₁ = (W⁄(W⁄K).FunctionField).a₁ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₁).symm
      have e2 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₂ = (W⁄(W⁄K).FunctionField).a₂ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₂).symm
      have e3 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₃ = (W⁄(W⁄K).FunctionField).a₃ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₃).symm
      have e4 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₄ = (W⁄(W⁄K).FunctionField).a₄ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₄).symm
      have e6 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₆ = (W⁄(W⁄K).FunctionField).a₆ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₆).symm
      rw [e1, e2, e3, e4, e6]
      linear_combination heq
  have hdy : (minpoly K Q.yc).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy)
  obtain ⟨b, hb⟩ : Q.yc ∈ (algebraMap K (W⁄K).FunctionField).range :=
      minpoly.mem_range_of_degree_eq_one K _ hdy
  have hab : (W⁄K).Equation a b := by
    rw [← baseChange_equation W (Algebra.ofId K (W⁄K).FunctionField).injective a b]
    change (W⁄(W⁄K).FunctionField).Equation (algebraMap K _ a) (algebraMap K _ b)
    rw [ha, hb]
    exact (Point.nonsingular_xc_yc hQ).left
  have hns : (W⁄K).Nonsingular a b := (equation_iff_nonsingular (W := W⁄K)).mp hab
  refine ⟨.some a b hns, ?_⟩
  rw [Point.eq_some_xc_yc hQ, Point.baseChange, Point.map_some]
  congr 1 <;> [exact ha.symm; exact hb.symm]

theorem not_isIntegral_xc_of_ne_baseChange [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hQK : ∀ P : (W⁄K).Point, Q ≠ Point.baseChange K (W⁄K).FunctionField P) :
    ¬ _root_.IsIntegral K Q.xc :=
  fun hx => by obtain ⟨P, hP⟩ := exists_eq_baseChange_of_isIntegral_xc Q hQ hx; exact hQK P hP

end PointHom

section TransMul

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

omit [IsAlgClosed K] in
theorem genericPoint_ne_baseChange (P : (W⁄K).Point) :
    genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  cases P with
  | zero => exact Point.some_ne_zero _ (h.trans (map_zero _))
  | some a b hab =>
    rw [genericPoint, Point.baseChange, Point.map_some, Point.some.injEq] at h
    apply CoordinateRing.XClass_ne_zero (W' := W⁄K) a
    apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
    rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero]
    have h1 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X)) =
        genericX W K := rfl
    have h2 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField
        (CoordinateRing.mk (W⁄K) (C (C a))) =
        algebraMap K (W⁄K).FunctionField a :=
      (IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField a).symm
    rw [h1, h2, h.1, sub_eq_zero]
    rfl

omit [IsAlgClosed K] in
theorem genericPoint_add_baseChange_ne_zero (S : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ 0 := by
  intro h
  apply genericPoint_ne_baseChange W K (-S)
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

omit [IsAlgClosed K] in
theorem genericPoint_add_baseChange_ne_baseChange (S P : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ Point.baseChange K _ P := by
  intro h
  apply genericPoint_ne_baseChange W K (P - S)
  rw [map_sub, ← h, add_sub_cancel_right]

theorem transHom_injective (S : (W⁄K).Point) :
    Function.Injective (pointHom (genericPoint W K + Point.baseChange K _ S)
      (genericPoint_add_baseChange_ne_zero W K S)) :=
  pointHom_injective_of_ne_baseChange _ _ (genericPoint_add_baseChange_ne_baseChange W K S)

/-- **Pullback along a translation.** For an elliptic curve `W`, an algebraically closed field `K`
and a point `S ∈ W(K)`, the pullback of functions along `P ↦ P + S`, given by the point
`genericPoint W K + S'` over the function field of `W⁄K`, where `S'` is the base change of `S`. -/
noncomputable def transPull (S : (W⁄K).Point) : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

theorem map_transPull_genericPoint (S : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K) = genericPoint W K + Point.baseChange K _ S :=
  map_pointPull_genericPoint _ _ _

theorem map_transPull_genericPoint_add (S T : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K + Point.baseChange K _ T) =
      genericPoint W K + Point.baseChange K _ (S + T) := by
  rw [map_add, map_transPull_genericPoint, Point.map_baseChange, add_assoc, ← map_add]

theorem transPull_comp_algebraMap (S : (W⁄K).Point) :
    (transPull W K S : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (genericPoint W K + Point.baseChange K _ S)
          (genericPoint_add_baseChange_ne_zero W K S) :=
  pointPull_comp_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

theorem transPull_comp_pointHom (S : (W⁄K).Point) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (transPull W K S) P ≠ 0) :
    (transPull W K S).comp (pointHom P hP) = pointHom (Point.map (transPull W K S) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

theorem transPull_comp_transHom (S T : (W⁄K).Point) :
    (transPull W K S).comp (pointHom (genericPoint W K + Point.baseChange K _ T)
      (genericPoint_add_baseChange_ne_zero W K T)) =
      pointHom (genericPoint W K + Point.baseChange K _ (S + T))
        (genericPoint_add_baseChange_ne_zero W K (S + T)) := by
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, ← map_transPull_genericPoint_add,
      Point.xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, ← map_transPull_genericPoint_add,
      Point.yc_map]

theorem transPull_comp (S T : (W⁄K).Point) :
    (transPull W K S).comp (transPull W K T) = transPull W K (S + T) := by
  apply FunctionField.algHom_ext
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, transPull_comp_algebraMap W K T,
    transPull_comp_algebraMap W K (S + T), ← AlgHom.comp_toRingHom, transPull_comp_transHom]

theorem transPull_zero : transPull W K 0 = AlgHom.id K _ := by
  apply FunctionField.algHom_ext
  rw [transPull_comp_algebraMap]
  have h0 : genericPoint W K + Point.baseChange K (W⁄K).FunctionField (0 : (W⁄K).Point) =
      genericPoint W K := by
    rw [map_zero, add_zero]
  rw [pointHom_congr h0 _ (Point.some_ne_zero _), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

/-- **Translation automorphism.** For an elliptic curve `W`, an algebraically closed field `K` and
a point `S ∈ W(K)`, `transPull W K S` as a `K`-algebra automorphism of the function field of
`W⁄K`, with inverse `transPull W K (-S)`. -/
noncomputable def transEquiv (S : (W⁄K).Point) : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (transPull W K S) (transPull W K (-S))
    (by rw [transPull_comp, add_neg_cancel, transPull_zero])
    (by rw [transPull_comp, neg_add_cancel, transPull_zero])

theorem transEquiv_apply (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    transEquiv W K S h = transPull W K S h := rfl

theorem coe_transEquiv (S : (W⁄K).Point) :
    (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = transPull W K S := rfl

theorem transEquiv_algebraMap (S : (W⁄K).Point) (h : (W⁄K).CoordinateRing) :
    transEquiv W K S (algebraMap _ _ h) =
      pointHom (genericPoint W K + Point.baseChange K _ S)
          (genericPoint_add_baseChange_ne_zero W K S) h :=
  pointPull_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S) h

theorem transEquiv_genericX (S : (W⁄K).Point) :
    transEquiv W K S (genericX W K) = (genericPoint W K + Point.baseChange K _ S).xc := by
  rw [genericX, transEquiv_algebraMap, pointHom_mk_C_X]

theorem transEquiv_genericY (S : (W⁄K).Point) :
    transEquiv W K S (genericY W K) = (genericPoint W K + Point.baseChange K _ S).yc := by
  rw [genericY, transEquiv_algebraMap, pointHom_mk_Y]

theorem map_transEquiv_genericPoint (S : (W⁄K).Point) :
    Point.map (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K)
        =
      genericPoint W K + Point.baseChange K _ S := by
  rw [coe_transEquiv, map_transPull_genericPoint]

theorem transEquiv_add (S T : (W⁄K).Point) :
    transEquiv W K (S + T) = (transEquiv W K T).trans (transEquiv W K S) := by
  apply AlgEquiv.ext
  intro h
  rw [AlgEquiv.trans_apply, transEquiv_apply, transEquiv_apply, transEquiv_apply,
    ← AlgHom.comp_apply, transPull_comp]

theorem transEquiv_zero : transEquiv W K 0 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro h
  rw [transEquiv_apply, transPull_zero]
  rfl

theorem transEquiv_injective : Function.Injective (transEquiv W K) := by
  intro S T h
  have hx := transEquiv_genericX W K S
  have hy := transEquiv_genericY W K S
  rw [h, transEquiv_genericX] at hx
  rw [h, transEquiv_genericY] at hy
  have hpt : genericPoint W K + Point.baseChange K _ T = genericPoint W K + Point.baseChange K _ S
      := by
    rw [Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K T),
      Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K S)]
    congr 1
  exact (Point.map_injective _ (add_left_cancel hpt)).symm

omit [IsAlgClosed K] in
theorem neg_genericPoint_ne_baseChange (P : (W⁄K).Point) :
    -genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  apply genericPoint_ne_baseChange W K (-P)
  rw [map_neg, ← h, neg_neg]

theorem negHom_injective :
    Function.Injective (pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _))) :=
  pointHom_injective_of_ne_baseChange _ _ (neg_genericPoint_ne_baseChange W K)

/-- **Pullback along negation.** For an elliptic curve `W` and an algebraically closed field `K`,
the pullback of functions along `P ↦ -P`. -/
noncomputable def negPull : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (neg_ne_zero.mpr (Point.some_ne_zero _)) (negHom_injective W K)

theorem map_negPull_genericPoint : Point.map (negPull W K) (genericPoint W K) = -genericPoint W K :=
  map_pointPull_genericPoint _ _ _

theorem negPull_algebraMap (g : (W⁄K).CoordinateRing) :
    negPull W K (algebraMap _ _ g) = pointHom (-genericPoint W K)
        (neg_ne_zero.mpr (Point.some_ne_zero _)) g :=
  pointPull_algebraMap _ _ _ g

theorem negPull_comp_algebraMap :
    (negPull W K : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _)) :=
  pointPull_comp_algebraMap _ _ _

theorem negPull_comp_pointHom (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (negPull W K) P ≠ 0) :
    (negPull W K).comp (pointHom P hP) = pointHom (Point.map (negPull W K) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

theorem negPull_comp_negPull : (negPull W K).comp (negPull W K) = AlgHom.id K _ := by
  apply FunctionField.algHom_ext
  have hP' : Point.map (negPull W K) (-genericPoint W K) = genericPoint W K := by
    rw [map_neg, map_negPull_genericPoint, neg_neg]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, negPull_comp_algebraMap, ← AlgHom.comp_toRingHom,
    negPull_comp_pointHom W K _ _ (by rw [hP']; exact Point.some_ne_zero _),
    pointHom_congr hP' _ (Point.some_ne_zero _), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

/-- **Negation automorphism.** For an elliptic curve `W` and an algebraically closed field `K`,
`negPull W K` as a `K`-algebra automorphism; it is its own inverse. -/
noncomputable def negEquiv : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (negPull W K) (negPull W K) (negPull_comp_negPull W K)
      (negPull_comp_negPull W K)

theorem coe_negEquiv : (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = negPull W K
    := rfl

theorem negEquiv_apply (h : (W⁄K).FunctionField) : negEquiv W K h = negPull W K h := rfl

theorem map_negEquiv_genericPoint :
    Point.map (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K) =
      -genericPoint W K := by
  rw [coe_negEquiv, map_negPull_genericPoint]

theorem negEquiv_genericX : negEquiv W K (genericX W K) = genericX W K := by
  rw [negEquiv_apply, genericX, negPull_algebraMap, pointHom_mk_C_X]
  simp only [genericPoint, Point.neg_some, Point.xc_some]
  rfl

theorem negEquiv_genericY :
    negEquiv W K (genericY W K) = (W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) := by
  rw [negEquiv_apply, genericY, negPull_algebraMap, pointHom_mk_Y]
  simp only [genericPoint, Point.neg_some, Point.yc_some]
  rfl

theorem negEquiv_symm : (negEquiv W K).symm = negEquiv W K := rfl

/-- **Admissible multiplier.** For an elliptic curve `W`, `MulGood W K n` means that
`n • genericPoint W K` is nonzero and is not the base change of any point of `W` over `K`. This is
the condition `mulPull W K n` needs. It fails for `n = 0`; `zsmul_genericPoint_good` shows that it
holds when `K` is algebraically closed and `(n : K) ≠ 0`. -/
def MulGood (n : ℤ) : Prop :=
  n • genericPoint W K ≠ 0 ∧
    ∀ P : (W⁄K).Point, n • genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P

theorem mulHom_injective {n : ℤ} (h : MulGood W K n) :
    Function.Injective (pointHom (n • genericPoint W K) h.1) :=
  pointHom_injective_of_ne_baseChange _ _ h.2

/-- **Pullback along multiplication by `n`.** For an elliptic curve `W` and an algebraically closed
field `K`, the pullback of functions along `P ↦ n • P`, given by the point `n • genericPoint W K`;
it takes a proof of `MulGood W K n`. -/
noncomputable def mulPull (n : ℤ) (h : MulGood W K n) :
    (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h)

theorem mulPull_eq {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h = pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h) := rfl

theorem mulPull_algebraMap {n : ℤ} (h : MulGood W K n) (g : (W⁄K).CoordinateRing) :
    mulPull W K n h (algebraMap _ _ g) = pointHom (n • genericPoint W K) h.1 g := by
  rw [mulPull_eq W K h, pointPull_algebraMap]

theorem mulPull_comp_algebraMap {n : ℤ} (h : MulGood W K n) :
    (mulPull W K n h : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) = pointHom (n • genericPoint W K) h.1 :=
  RingHom.ext fun g => mulPull_algebraMap W K h g

theorem mulPull_genericX' {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h (genericX W K) = (n • genericPoint W K).xc := by
  rw [genericX, mulPull_algebraMap W K h, pointHom_mk_C_X]

theorem mulPull_genericY' {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h (genericY W K) = (n • genericPoint W K).yc := by
  rw [genericY, mulPull_algebraMap W K h, pointHom_mk_Y]

theorem map_mulPull_genericPoint' {n : ℤ} (h : MulGood W K n) :
    Point.map (mulPull W K n h) (genericPoint W K) = n • genericPoint W K := by
  rw [mulPull_eq W K h, map_pointPull_genericPoint]

theorem mulPull_comp_pointHom {n : ℤ} (h : MulGood W K n) (P : (W⁄(W⁄K).FunctionField).Point)
    (hP : P ≠ 0) (hP' : Point.map (mulPull W K n h) P ≠ 0) :
    (mulPull W K n h).comp (pointHom P hP) = pointHom (Point.map (mulPull W K n h) P) hP' := by
  have hP'' : Point.map (pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h)) P ≠ 0 := by
    rw [← mulPull_eq W K h]; exact hP'
  rw
      [pointHom_congr (congrArg (fun φ => Point.map φ P) (mulPull_eq W K h)) hP' hP'', mulPull_eq W
        K h]
  exact pointPull_comp_pointHom _ _ _ P hP hP''

theorem transEquiv_mulPull' {n : ℤ} (h : MulGood W K n) {S : (W⁄K).Point} (hS : n • S = 0)
    (g : (W⁄K).FunctionField) : transEquiv W K S (mulPull W K n h g) = mulPull W K n h g := by
  rw [transEquiv_apply, ← AlgHom.comp_apply]
  congr 1
  apply FunctionField.algHom_ext
  have hP' : Point.map (transPull W K S) (n • genericPoint W K) = n • genericPoint W K := by
    rw [map_zsmul, map_transPull_genericPoint, smul_add, ← map_zsmul, hS, map_zero, add_zero]
  rw
      [AlgHom.comp_toRingHom, RingHom.comp_assoc, mulPull_comp_algebraMap W K h, ←
        AlgHom.comp_toRingHom,
    transPull_comp_pointHom W K S _ _ (by rw [hP']; exact h.1)]
  exact congrArg _ (pointHom_congr hP' _ _)

theorem mulPull_comp' {m n : ℤ} (hm : MulGood W K m) (hn : MulGood W K n)
    (hnm : MulGood W K (n * m)) :
    (mulPull W K m hm).comp (mulPull W K n hn) = mulPull W K (n * m) hnm := by
  apply FunctionField.algHom_ext
  have hP' : Point.map (mulPull W K m hm) (n • genericPoint W K) = (n * m) • genericPoint W K := by
    rw [map_zsmul, map_mulPull_genericPoint' W K hm, smul_smul]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, mulPull_comp_algebraMap W K hn,
    mulPull_comp_algebraMap W K hnm, ← AlgHom.comp_toRingHom,
    mulPull_comp_pointHom W K hm _ _ (by rw [hP']; exact hnm.1)]
  exact congrArg _ (pointHom_congr hP' _ _)

omit [DecidableEq K] in
theorem exists_point_xc_eq (x : K) : ∃ P : (W⁄K).Point, P ≠ 0 ∧ P.xc = x := by
  have : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  set c := (W⁄K).a₁ * x + (W⁄K).a₃ with hc
  set d := -(x ^ 3 + (W⁄K).a₂ * x ^ 2 + (W⁄K).a₄ * x + (W⁄K).a₆) with hd
  have hlt : (C c * X + C d : K[X]).degree < ((X : K[X]) ^ 2).degree := by
    rw [degree_X_pow]
    refine (degree_add_le _ _).trans_lt (max_lt ((degree_C_mul_X_le c).trans_lt ?_)
      (degree_C_le.trans_lt ?_))
    · exact WithBot.coe_lt_coe.mpr (by norm_num)
    · exact WithBot.coe_lt_coe.mpr (by norm_num)
  have hdeg : ((X : K[X]) ^ 2 + (C c * X + C d)).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]; rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root ((X : K[X]) ^ 2 + (C c * X + C d))
    (by rw [hdeg]; exact two_ne_zero)
  have hroot : y ^ 2 + (c * y + d) = 0 := by
    have := hy.eq_zero
    simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C] using this
  have heq : (W⁄K).Equation x y := by
    rw [equation_iff]
    rw [hc, hd] at hroot
    linear_combination hroot
  exact ⟨.some x y ((equation_iff_nonsingular (W := W⁄K)).mp heq), Point.some_ne_zero _, rfl⟩

omit [DecidableEq K] in
theorem infinite_point : Infinite (W⁄K).Point := by
  choose f hf0 hfx using exists_point_xc_eq W K
  exact Infinite.of_injective f fun x y h => by rw [← hfx x, ← hfx y, h]

theorem map_negEquiv_zsmul_genericPoint (n : ℤ) :
    Point.map (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (n • genericPoint W K)
        =
      -(n • genericPoint W K) := by
  rw [map_zsmul, map_negEquiv_genericPoint, smul_neg]

theorem negEquiv_mulPull_genericX' {n : ℤ} (h : MulGood W K n) :
    negEquiv W K (mulPull W K n h (genericX W K)) = (n • genericPoint W K).xc := by
  rw [mulPull_genericX' W K h, ← AlgEquiv.coe_toAlgHom, ← Point.xc_map (W := W) (K := K),
    map_negEquiv_zsmul_genericPoint, Point.eq_some_xc_yc h.1, Point.neg_some, Point.xc_some,
        Point.xc_some]

theorem negEquiv_mulPull_genericY' {n : ℤ} (h : MulGood W K n) :
    negEquiv W K (mulPull W K n h (genericY W K)) =
      (W⁄(W⁄K).FunctionField).negY (n • genericPoint W K).xc (n • genericPoint W K).yc := by
  rw [mulPull_genericY' W K h, ← AlgEquiv.coe_toAlgHom, ← Point.yc_map (W := W) (K := K),
    map_negEquiv_zsmul_genericPoint]
  conv_lhs => rw [Point.eq_some_xc_yc h.1, Point.neg_some, Point.yc_some]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem mulPull_injective [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ}
    (h : MulGood W K n) : Function.Injective (mulPull W K n h) := (mulPull W K n h).injective

end TransMul

section Places

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

/-- **The place of an affine point.** For a nonzero point `P` of `W⁄K`, that is, a nonsingular
affine point `(x, y)` over `K`, the maximal ideal of the coordinate ring of `W⁄K` generated by
`X - x` and `Y - y`, as a height-one prime. -/
noncomputable def placeOf (P : (W⁄K).Point) (hP : P ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc)
  isPrime := (CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hP).left).isPrime
  ne_bot h := CoordinateRing.XClass_ne_zero (W' := W⁄K) P.xc
    (by rw [← Ideal.mem_bot, ← h]; exact Ideal.subset_span (Set.mem_insert _ _))

omit [DecidableEq K] in
@[simp] theorem placeOf_asIdeal (P : (W⁄K).Point) (hP : P ≠ 0) :
    (placeOf W K P hP).asIdeal = CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) := rfl

omit [DecidableEq K] in
theorem placeOf_surjective [IsAlgClosed K] [W.IsElliptic]
    (v : IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing) :
    ∃ (P : (W⁄K).Point) (hP : P ≠ 0), placeOf W K P hP = v := by
  have : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have := v.isPrime
  obtain ⟨a, b, hab, hv⟩ := CoordinateRing.exists_eq_XYIdeal v.ne_bot
  refine ⟨.some a b ((equation_iff_nonsingular (W := W⁄K)).mp hab), Point.some_ne_zero _, ?_⟩
  exact IsDedekindDomain.HeightOneSpectrum.ext hv.symm

/-- **Evaluation at a solution of the curve equation.** For `a` and `b` in `K` that satisfy the
equation of `W⁄K`, singular or not, the ring map from the coordinate ring of `W⁄K` to `K` that
sends `X` to `a` and `Y` to `b`. -/
noncomputable def CoordinateRing.evalAt {a b : K} (h : (W⁄K).Equation a b) :
    (W⁄K).CoordinateRing →+* K :=
  AdjoinRoot.evalEval h

omit [DecidableEq K] in
theorem CoordinateRing.evalAt_mk {a b : K} (h : (W⁄K).Equation a b) (g : K[X][Y]) :
    CoordinateRing.evalAt W K h (CoordinateRing.mk (W⁄K) g) = g.evalEval a b :=
  AdjoinRoot.evalEval_mk h g

omit [DecidableEq K] in
theorem CoordinateRing.evalAt_XYIdeal {a b : K} (h : (W⁄K).Equation a b) :
    ∀ g ∈ CoordinateRing.XYIdeal (W⁄K) a (C b), CoordinateRing.evalAt W K h g = 0 := by
  intro g hg
  rw [← RingHom.mem_ker]
  revert hg g
  rw [← IsConcreteLE.le_iff, CoordinateRing.XYIdeal, Ideal.span_le]
  rintro g (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.XClass, CoordinateRing.evalAt_mk,
      evalEval_C, eval_sub, eval_X, eval_C, sub_self]
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.YClass, CoordinateRing.evalAt_mk,
      evalEval_sub, evalEval_X, evalEval_C, eval_C, sub_self]

omit [DecidableEq K] in
theorem placeOf_injective {P Q : (W⁄K).Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : placeOf W K P hP = placeOf W K Q hQ) : P = Q := by
  obtain ⟨hx, hy⟩ := (CoordinateRing.XYIdeal_eq_XYIdeal_iff (Point.nonsingular_xc_yc hP).left
    Q.xc Q.yc).mp (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  rw [Point.eq_some_xc_yc hP, Point.eq_some_xc_yc hQ]
  congr 1

end Places

end WeierstrassCurve.Affine

open Polynomial

namespace Valuation

variable {L : Type*} [CommRing L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀)

/-- **Congruence for a valuation.** `a` and `b` are congruent for `v` when `v (a - b) < 1`. -/
def Cong (a b : L) : Prop := v (a - b) < 1

variable {v}

theorem cong_iff {a b : L} : v.Cong a b ↔ v (a - b) < 1 := Iff.rfl

@[refl] theorem Cong.refl (a : L) : v.Cong a a := by simp [Cong]

theorem Cong.rfl {a : L} : v.Cong a a := Cong.refl a

@[symm] theorem Cong.symm {a b : L} (h : v.Cong a b) : v.Cong b a := by
  rw [Cong, ← Valuation.map_neg, neg_sub]; exact h

theorem Cong.trans {a b c : L} (h₁ : v.Cong a b) (h₂ : v.Cong b c) : v.Cong a c := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

theorem Cong.add {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a + b) (a' + b') :=
    by
  have : a + b - (a' + b') = (a - a') + (b - b') := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

theorem Cong.neg {a a' : L} (h : v.Cong a a') : v.Cong (-a) (-a') := by
  have : -a - -a' = -(a - a') := by ring
  rw [Cong, this, Valuation.map_neg]; exact h

theorem Cong.sub {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a - b) (a' - b') :=
    by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h₁.add h₂.neg

theorem Cong.le_one {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) : v a ≤ 1 := by
  have : a = (a - a') + a' := by ring
  rw [this]
  exact (v.map_add _ _).trans (max_le h.le ha')

theorem Cong.mul {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') (ha' : v a' ≤ 1)
    (hb' : v b' ≤ 1) : v.Cong (a * b) (a' * b') := by
  have ha : v a ≤ 1 := h₁.le_one ha'
  have : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [Cong, this]
  refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul]
    calc v a * v (b - b') ≤ 1 * v (b - b') := mul_le_mul' ha le_rfl
      _ < 1 := by rw [one_mul]; exact h₂
  · rw [Valuation.map_mul]
    calc v (a - a') * v b' ≤ v (a - a') * 1 := mul_le_mul' le_rfl hb'
      _ < 1 := by rw [mul_one]; exact h₁

theorem Cong.pow {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (n : ℕ) : v.Cong (a ^ n) (a' ^ n) :=
    by
  induction n with
  | zero => simp only [pow_zero]; exact Cong.rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h (by rw [Valuation.map_pow]; exact pow_le_one' ha' n) ha'

theorem Cong.eq_of_eq_one {a a' : L} (h : v.Cong a a') (ha' : v a' = 1) : v a = 1 := by
  have : a = a' + (a - a') := by ring
  rw [this, Valuation.map_add_eq_of_lt_left]
  · exact ha'
  · rw [ha']; exact h

theorem Cong.lt_one_iff {a a' : L} (h : v.Cong a a') : v a < 1 ↔ v a' < 1 := by
  constructor
  · intro ha
    have : a' = a - (a - a') := by ring
    rw [this]
    exact (v.map_sub _ _).trans_lt (max_lt ha h)
  · intro ha'
    have : a = (a - a') + a' := by ring
    rw [this]
    exact (v.map_add _ _).trans_lt (max_lt h ha')

theorem cong_zero_iff {a : L} : v.Cong a 0 ↔ v a < 1 := by rw [Cong, sub_zero]

section Field

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}

theorem Cong.inv {d d' : F} (h : w.Cong d d') (hd' : w d' = 1) : w.Cong d⁻¹ d'⁻¹ := by
  have hd : w d = 1 := h.eq_of_eq_one hd'
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd; exact zero_ne_one hd
  have hd0' : d' ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd'; exact zero_ne_one hd'
  have : d⁻¹ - d'⁻¹ = -(d - d') * (d⁻¹ * d'⁻¹) := by
    field_simp
    ring
  rw
      [Cong, this, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, map_inv₀, map_inv₀, hd,
        hd',
    inv_one, mul_one, mul_one]
  exact h

theorem Cong.div {a d a' d' : F} (h₁ : w.Cong a a') (h₂ : w.Cong d d') (ha' : w a' ≤ 1)
    (hd' : w d' = 1) : w.Cong (a / d) (a' / d') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h₁.mul (h₂.inv hd') ha' (by rw [map_inv₀, hd', inv_one])

end Field

section Eval

variable {K : Type*} [CommRing K] (f : K →+* L)

theorem Cong.eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (p : K[X])
    :
    v.Cong (p.eval₂ f a) (p.eval₂ f a') ∧ v (p.eval₂ f a') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n c =>
    rw [eval₂_monomial, eval₂_monomial]
    have hpow : v (a' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' ha' n
    exact ⟨(Cong.refl (f c)).mul (h.pow ha' n) (hf c) hpow,
      by rw [Valuation.map_mul]; exact mul_le_one' (hf c) hpow⟩

theorem Cong.eval₂_eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' b b' : L} (ha : v.Cong a a') (ha' : v a' ≤ 1)
    (hb : v.Cong b b') (hb' : v b' ≤ 1) (p : K[X][X]) :
    v.Cong (p.eval₂ (eval₂RingHom f a) b) (p.eval₂ (eval₂RingHom f a') b') ∧
      v (p.eval₂ (eval₂RingHom f a') b') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n q =>
    rw [eval₂_monomial, eval₂_monomial, coe_eval₂RingHom, coe_eval₂RingHom]
    have hq := Cong.eval₂ f hf ha ha' q
    have hpow : v (b' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' hb' n
    exact
        ⟨hq.1.mul (hb.pow hb' n) hq.2 hpow, by rw [Valuation.map_mul]; exact mul_le_one' hq.2 hpow⟩

end Eval

end Valuation

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {R' : Type*} [CommRing R'] [IsDedekindDomain R'] {K' : Type*} [Field K']
  [Algebra R' K'] [IsFractionRing R' K']

omit [IsDedekindDomain R] [IsFractionRing R K] in
theorem valuation_map_le_exp_neg_of_mem_pow (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1)
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (m : ℕ) : ∀ a ∈ w.asIdeal ^ m, v.valuation K' (ψ (algebraMap R K a)) ≤ exp (-(m : ℤ)) := by
  induction m with
  | zero =>
    intro a _
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact h0 a
  | succ m ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro c hc a' ha'
      rw [map_mul, map_mul, map_mul, Nat.cast_succ, neg_add, add_comm, exp_add]
      exact mul_le_mul' (h1 c hc) (ih a' ha')
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add, map_add]
      exact (Valuation.map_add _ _ _).trans (max_le hz₁ hz₂)

theorem valuation_map_le_of_valuation_le (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (h2 : ∀ b : R, b ∉ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) = 1)
    (x : K) (k : ℕ) (hx : w.valuation K x ≤ exp (-(k : ℤ))) :
    v.valuation K' (ψ x) ≤ exp (-(k : ℤ)) := by
  have h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1 := by
    intro b
    by_cases hb : b ∈ w.asIdeal
    · exact (h1 b hb).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
    · exact (h2 b hb).le
  have hx1 : w.valuation K x ≤ 1 :=
    hx.trans (by rw [← exp_zero, exp_le_exp, neg_nonpos]; exact Nat.cast_nonneg k)
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer (v := w) x hx1
  have hd : (d : R) ∉ w.asIdeal := d.2
  have hwn : w.valuation K (algebraMap R K n) ≤ exp (-(k : ℤ)) := by
    rw [← hnd, map_mul, (valuation_eq_one_iff_notMem (K := K) w).mpr hd, mul_one]
    exact hx
  rw [valuation_of_algebraMap, intValuation_le_pow_iff_mem] at hwn
  have hψn := valuation_map_le_exp_neg_of_mem_pow ψ w v h0 h1 k n hwn
  have := congrArg (fun t => v.valuation K' (ψ t)) hnd
  simp only [map_mul, h2 d hd, mul_one] at this
  rw [this]
  exact hψn

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

section Transport

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

theorem _root_.WithZero.lt_one_iff_le_exp_neg_one {y : ℤᵐ⁰} : y < 1 ↔ y ≤ exp (-1 : ℤ) := by
  by_cases hy : y = 0
  · subst hy; simp
  · rw [← exp_log hy, ← exp_zero, exp_lt_exp, exp_le_exp]; omega

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem valuation_algebraMap_le_one (P : (W⁄K).Point) (hP : P ≠ 0) (c : K) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField]
  exact valuation_le_one _ _

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem valuation_algebraMap_eq_one (P : (W⁄K).Point) (hP : P ≠ 0) {c : K} (hc : c ≠ 0) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) = 1 := by
  apply le_antisymm (valuation_algebraMap_le_one W K P hP c)
  have h := valuation_algebraMap_le_one W K P hP c⁻¹
  rw [map_inv₀, map_inv₀, inv_le_one₀] at h
  · exact h
  · rw [Valuation.pos_iff]
    exact (_root_.map_ne_zero _).mpr hc

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem mem_placeOf_iff (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    b ∈ (placeOf W K P hP).asIdeal ↔ CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left b =
        0 := by
  constructor
  · exact CoordinateRing.evalAt_XYIdeal W K _ b
  · intro hb
    have hker : RingHom.ker (CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left) =
        (placeOf W K P hP).asIdeal := by
      refine ((CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hP).left).eq_of_le
        (RingHom.ker_ne_top _) ?_).symm
      intro g hg
      exact (RingHom.mem_ker).mpr (CoordinateRing.evalAt_XYIdeal W K _ g hg)
    rw [← hker]
    exact (RingHom.mem_ker).mpr hb

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem cong_genericX (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericX W K)
      (algebraMap K (W⁄K).FunctionField P.xc) := by
  rw
      [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing
        (W⁄K).FunctionField, genericX,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) (C X) - algebraMap K (W⁄K).CoordinateRing P.xc =
      CoordinateRing.XClass (W⁄K) P.xc := by
    rw [CoordinateRing.XClass, map_sub, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert _ _)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem cong_genericY (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericY W K)
      (algebraMap K (W⁄K).FunctionField P.yc) := by
  rw
      [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing
        (W⁄K).FunctionField, genericY,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) Y - algebraMap K (W⁄K).CoordinateRing P.yc =
      CoordinateRing.YClass (W⁄K) (C P.yc) := by
    rw [CoordinateRing.YClass, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem algebraMap_evalEval (g : K[X][Y]) (a b : K) :
    algebraMap K (W⁄K).FunctionField (g.evalEval a b) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a))
          (algebraMap K _ b) := by
  have hφ : (algebraMap K (W⁄K).FunctionField).comp (evalEvalRingHom a b) =
      eval₂RingHom (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a))
          (algebraMap K _ b) := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C, coe_eval₂RingHom,
        eval₂_C, eval₂_at_apply]
    · simp only
        [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X, eval_C, coe_eval₂RingHom,
        eval₂_X]
  exact RingHom.congr_fun hφ g

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem pointHom_mk_eq_eval₂ (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : K[X][Y]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) Q.xc) Q.yc := by
  rw [pointHom_mk]
  congr 1

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem valuation_pointPull_le (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) {P : (W⁄K).Point} (hP : P ≠ 0) {P' : (W⁄K).Point}
    (hP' : P' ≠ 0)
    (hx : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.xc (algebraMap K _ P'.xc))
    (hy : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.yc (algebraMap K _ P'.yc))
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K P' hP').valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (pointPull Q hQ hinj h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc : ∀ g : K[X][Y], v.Cong (pointHom Q hQ (CoordinateRing.mk (W⁄K) g))
      (algebraMap K _ (g.evalEval P'.xc P'.yc)) := by
    intro g
    rw [pointHom_mk_eq_eval₂, algebraMap_evalEval]
    exact
        (Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) (valuation_algebraMap_le_one W K P hP)
      hx (valuation_algebraMap_le_one W K P hP _) hy (valuation_algebraMap_le_one W K P hP _) g).1
  refine valuation_map_le_of_valuation_le
      (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField)
    (placeOf W K P' hP') (placeOf W K P hP) ?_ ?_ h k hh
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) ≤ _
    rw [pointPull_algebraMap, ← lt_one_iff_le_exp_neg_one, ← Valuation.cong_zero_iff]
    have h0 : g.evalEval P'.xc P'.yc = 0 := by
      rw [← CoordinateRing.evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact (mem_placeOf_iff W K P' hP' _).mp hb
    simpa only [h0, map_zero] using hc g
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) = 1
    rw [pointPull_algebraMap]
    have h0 : g.evalEval P'.xc P'.yc ≠ 0 := by
      rw [← CoordinateRing.evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact fun h => hb ((mem_placeOf_iff W K P' hP' _).mpr h)
    exact (hc g).eq_of_eq_one (valuation_algebraMap_eq_one W K P hP h0)

theorem valuation_mulPull_le {n : ℤ} (hgood : MulGood W K n) (Φ Ψ : K[X]) (ω ψ : K[X][Y])
    (hξ : (n • genericPoint W K).xc =
      Φ.eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K) /
        Ψ.eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K))
    (hη : (n • genericPoint W K).yc =
      ω.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (genericX W K)) (genericY W K) /
        ψ.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (genericX W K)) (genericY W K) ^ 3)
    {P : (W⁄K).Point} (hP : P ≠ 0) (hnP : n • P ≠ 0)
    (hxP : (n • P).xc = Φ.eval P.xc / Ψ.eval P.xc) (hΨ : Ψ.eval P.xc ≠ 0)
    (hyP : (n • P).yc = ω.evalEval P.xc P.yc / ψ.evalEval P.xc P.yc ^ 3)
        (hψ : ψ.evalEval P.xc P.yc ≠ 0)
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K (n • P) hnP).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n hgood h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc1 := valuation_algebraMap_le_one W K P hP
  have hX := cong_genericX W K P hP
  have hY := cong_genericY W K P hP
  have hx : v.Cong (n • genericPoint W K).xc (algebraMap K _ (n • P).xc) := by
    rw [hξ, hxP, map_div₀, ← eval₂_at_apply, ← eval₂_at_apply]
    have hΦ := Valuation.Cong.eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) Φ
    have hΨc := Valuation.Cong.eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) Ψ
    refine hΦ.1.div hΨc.1 hΦ.2 ?_
    rw [eval₂_at_apply]
    exact valuation_algebraMap_eq_one W K P hP hΨ
  have hy : v.Cong (n • genericPoint W K).yc (algebraMap K _ (n • P).yc) := by
    rw [hη, hyP, map_div₀, map_pow, algebraMap_evalEval, algebraMap_evalEval]
    have hω := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) hY (hc1 _) ω
    have hψc := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) hY (hc1 _) ψ
    refine hω.1.div (hψc.1.pow hψc.2 3) hω.2 ?_
    rw [← algebraMap_evalEval, ← map_pow]
    exact valuation_algebraMap_eq_one W K P hP (pow_ne_zero 3 hψ)
  rw [mulPull_eq W K hgood]
  exact valuation_pointPull_le W K _ _ _ hP hnP hx hy h k hh

end Transport

end WeierstrassCurve.Affine

open WeierstrassCurve.Affine

namespace FunctionFieldPullback.NatDeg

open Polynomial

private theorem PortCard.natDegree_Φ_sub_C_mul_ΨSq {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) (n : ℤ) (c : R) :
    (W.Φ n - C c * W.ΨSq n).natDegree = n.natAbs ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [WeierstrassCurve.Φ_zero, WeierstrassCurve.ΨSq_zero, mul_zero, sub_zero, natDegree_one,
      Int.natAbs_zero, zero_pow two_ne_zero]
  · have h1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
    rw [natDegree_sub_eq_left_of_natDegree_lt, WeierstrassCurve.natDegree_Φ]
    calc (C c * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ ≤ n.natAbs ^ 2 - 1 := WeierstrassCurve.natDegree_ΨSq_le W n
      _ < n.natAbs ^ 2 := Nat.sub_lt (by omega) one_pos
      _ = (W.Φ n).natDegree := (WeierstrassCurve.natDegree_Φ W n).symm

private theorem solution {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ)
    (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 :=
  PortCard.natDegree_Φ_sub_C_mul_ΨSq W n c
end FunctionFieldPullback.NatDeg


/-- **Degree of `Φₙ - c * ΨSqₙ`.** Over a nontrivial commutative ring, `Φₙ - c * ΨSqₙ` has degree
`n ^ 2` for every constant `c`. -/
theorem WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) (n : ℤ) (c : R) :
    (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 :=
  FunctionFieldPullback.NatDeg.solution W n c

namespace FunctionFieldPullback.Psi2

open Polynomial

private theorem PortCard.Ψ₂Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h0
  rw [WeierstrassCurve.Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : F) = 0 := congrArg Cubic.a h0
  have hb₂ : W.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : W.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : F) = 0 := by
    have h22 : (2 : F) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : W.Δ = 0 := by
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
      from rfl]
    linear_combination (-W.b₂ * W.b₈ + 9 * W.b₄ * W.b₆) * hb₂ + (-27 * W.b₆) * hb₆ +
      (-4 * W.b₄ ^ 3) * h2
  exact W.isUnit_Δ.ne_zero hΔ

private theorem solution {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0
    :=
  PortCard.Ψ₂Sq_ne_zero_of_isElliptic W
end FunctionFieldPullback.Psi2


/-- **`Ψ₂Sq` is nonzero on an elliptic curve.** For an elliptic curve over a field `F`, the
polynomial `Ψ₂Sq` is nonzero. Its roots in an algebraic closure of `F` are the `x`-coordinates of
the geometric points of order two; a root in `F` need not be the `x`-coordinate of a point over
`F`. Mathlib's `WeierstrassCurve.Ψ₂Sq_ne_zero` assumes `(4 : R) ≠ 0` instead; this version uses
ellipticity, so it also covers characteristic two. -/
theorem WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] : W.Ψ₂Sq ≠ 0 :=
  FunctionFieldPullback.Psi2.solution W

namespace FunctionFieldPullback.ZsmulDiv

section PortCardMulX

namespace PortCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

private theorem zsmul_some_eq_some_of_evalEval_ψ_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧
        x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧
        x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have heq : W.toAffine.Equation x y := h.left
  have hψsq := W.evalEval_ψ_sq heq n
  have key := zsmul_eq_smulEval W h n
  have hVz : smulEval W x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨smulEval W x y n 0 / smulEval W x y n 2 ^ 2,
    smulEval W x y n 1 / smulEval W x y n 2 ^ 3,
    (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_, ?_⟩
  · calc n • Point.some x y h
        = Jacobian.Point.toAffineAddEquiv W
            (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply]
      _ = _ := by
          rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
          exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
  · change (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 2 =
        (W.φ n).evalEval x y
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
  · change (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ΨSq n).eval x = (W.Φ n).eval x
    rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), W.evalEval_φ heq]

private theorem zsmul_some_eq_some_of_eval_ΨSq_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧ x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have hψ : (W.ψ n).evalEval x y ≠ 0 := fun h0 =>
    hn (by rw [← W.evalEval_ψ_sq h.left n, h0]; exact zero_pow two_ne_zero)
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  exact ⟨x', y', h', hP, hx⟩

private theorem zsmul_some_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [Point.smul_some_eq_zero_iff W h n, ← W.evalEval_ψ_sq h.left n]
  exact ⟨fun h0 => by rw [h0]; exact zero_pow two_ne_zero, fun h0 => (sq_eq_zero_iff).mp h0⟩

private theorem zsmul_some_eq_some_div {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  have hΨ : (W.ΨSq n).eval x ≠ 0 := by
    rw [← W.evalEval_ψ_sq h.left n]; exact pow_ne_zero 2 hψ
  obtain rfl : x' = (W.Φ n).eval x / (W.ΨSq n).eval x := by rw [eq_div_iff hΨ]; exact hx
  exact ⟨y', h', hP⟩

end PortCard

end PortCardMulX

private theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F)
    (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n •
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some
    ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  PortCard.zsmul_some_eq_some_div W h hψ
end FunctionFieldPullback.ZsmulDiv


/-- **`x`-coordinate of `n • (x, y)`.** For a nonsingular point `(x, y)` of a Weierstrass curve `W`
over a field, if `ψₙ(x, y) ≠ 0`, then `n • (x, y)` is affine and has `x`-coordinate
`Φₙ(x) / ΨSqₙ(x)`: it equals `(Φₙ(x) / ΨSqₙ(x), y')` for some `y'`. -/
theorem WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  FunctionFieldPullback.ZsmulDiv.solution W h hψ

namespace FunctionFieldPullback.AdjoinTop

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

private theorem adjoin_mk_X_mk_Y {K : Type*} [Field K] (W : WeierstrassCurve K) :
    Algebra.adjoin K {CoordinateRing.mk W.toAffine (C X), CoordinateRing.mk W.toAffine Y} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X) with hx
  set y := CoordinateRing.mk W.toAffine Y with hy
  apply Algebra.eq_top_iff.mpr
  intro r
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    have hC : ∀ c : K[X], CoordinateRing.mk W.toAffine (C c) ∈ Algebra.adjoin K {x, y} := by
      intro c
      have : CoordinateRing.mk W.toAffine (C c) = aeval x c := by
        have h1 : (CoordinateRing.mk W.toAffine).comp C = (aeval x : K[X] →ₐ[K] _).toRingHom := by
          apply Polynomial.ringHom_ext
          · intro k
            rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
            rfl
          · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        exact congrArg (fun f : K[X] →+* _ => f c) h1
      rw [this]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        (Polynomial.aeval_mem_adjoin_singleton K x)
    induction p using Polynomial.induction_on with
    | C c => exact hC c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c _ =>
      rw [map_mul, map_pow]
      exact mul_mem (hC c)
        (pow_mem (Algebra.subset_adjoin (Set.mem_insert_of_mem x (Set.mem_singleton y))) _)

private theorem solution {K : Type*} [Field K] (W : WeierstrassCurve K) :
    IntermediateField.adjoin K
      {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)),
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X)
  set y := CoordinateRing.mk W.toAffine Y
  set S : IntermediateField K W.toAffine.FunctionField := IntermediateField.adjoin K
    {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField x,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField y} with hS
  have hR : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ S := by
    intro r
    let φ : W.toAffine.CoordinateRing →ₐ[K] W.toAffine.FunctionField :=
      IsScalarTower.toAlgHom K W.toAffine.CoordinateRing W.toAffine.FunctionField
    have hr : r ∈ (⊤ : Subalgebra K W.toAffine.CoordinateRing) := Algebra.mem_top
    rw [← adjoin_mk_X_mk_Y W] at hr
    have himg : φ r ∈ (Algebra.adjoin K {x, y}).map φ := Subalgebra.mem_map.mpr ⟨r, hr, rfl⟩
    rw [AlgHom.map_adjoin] at himg
    have hle : Algebra.adjoin K (φ '' {x, y}) ≤ S.toSubalgebra := by
      rw [Set.image_pair]
      exact IntermediateField.algebra_adjoin_le_adjoin K _
    exact hle himg
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  exact div_mem (hR a) (hR b)
end FunctionFieldPullback.AdjoinTop


/-- **The function field is generated by `x` and `y`.** For a Weierstrass curve `W` over a field
`K`, the function field of `W` is generated over `K` by the classes of `X` and `Y`. -/
theorem WeierstrassCurve.Affine.FunctionField.adjoin_X_Y_eq_top {K : Type*} [Field K]
    (W : WeierstrassCurve K) :
    IntermediateField.adjoin K
      {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)),
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ :=
  FunctionFieldPullback.AdjoinTop.solution W

namespace FunctionFieldPullback.Span

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace WeilPairingND

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDedekindDomain R] in
private lemma isUnit_of_forall_not_mem [IsDomain R] {r : R}
    (hr : ∀ w : HeightOneSpectrum R, r ∉ w.asIdeal)
    (w₀ : HeightOneSpectrum R) : IsUnit r := by
  by_contra hu
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {r}) (Ideal.span_singleton_ne_top hu)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr w₀ (Submodule.zero_mem _)
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => by
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hr0 hle
  exact hr ⟨𝔪, h𝔪.isPrime, h𝔪0⟩ (hle (Ideal.mem_span_singleton_self r))

private theorem exists_eq_span_of_eq_pullback (μ : K →+* K)
    (N : HeightOneSpectrum R → Option (HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w)
    (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ),
      w.valuation K h ≤ exp (-(k : ℤ)) → v.valuation K (μ h) ≤ exp (-(k : ℤ)))
    (g : K) (t₀ : HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = exp (-1))
    (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) :
    ∃ r : R, t₀.asIdeal = Ideal.span {r} := by
  obtain ⟨h, rfl⟩ := hgμ
  obtain ⟨v₀, hv₀⟩ := hN t₀
  have hg_le : ∀ v w, N v = some w → v.valuation K (μ h) ≤ 1 := by
    intro v w hvw
    by_cases hw : w = t₀
    · subst hw; rw [hg₀ v hvw, ← exp_zero, exp_le_exp]; norm_num
    · rw [hg₁ v w hvw hw]
  have hμ0 : ∀ v w, N v = some w → ∀ x : K, w.valuation K x ≤ 1 → v.valuation K (μ x) ≤ 1 := by
    intro v w hvw x hx
    have := hμ v w hvw x 0 (by rwa [Nat.cast_zero, neg_zero, exp_zero])
    rwa [Nat.cast_zero, neg_zero, exp_zero] at this
  have hh0 : h ≠ 0 := by
    rintro rfl
    have := hg₀ v₀ hv₀
    rw [map_zero, Valuation.map_zero] at this
    exact WithZero.zero_ne_coe this
  have hμh0 : μ h ≠ 0 := (map_ne_zero μ).mpr hh0
  have h1 : ∀ w : HeightOneSpectrum R, w.valuation K h ≤ 1 := by
    intro w
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hv⟩ := hN w
    have hinv : w.valuation K h⁻¹ ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one, map_inv₀]
      exact WithZero.lt_one_iff_le_exp_neg_one.mp ((inv_lt_one₀ (lt_trans zero_lt_one hlt)).mpr hlt)
    have := hμ v w hv h⁻¹ 1 hinv
    rw [map_inv₀, map_inv₀, Nat.cast_one] at this
    have hlt' : (v.valuation K (μ h))⁻¹ < 1 := lt_of_le_of_lt this (by
      rw [← exp_zero, exp_lt_exp]; norm_num)
    have hpos : 0 < v.valuation K (μ h) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hμh0)
    exact absurd ((inv_lt_one₀ hpos).mp hlt') (not_lt.mpr (hg_le v w hv))
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one K h h1
  subst hr
  have hr0 : r ≠ 0 := fun h0 => hh0 (by rw [h0, map_zero])
  have h3 : ∀ w : HeightOneSpectrum R, w ≠ t₀ → r ∉ w.asIdeal := by
    intro w hw hmem
    obtain ⟨v, hv⟩ := hN w
    have hlt : w.valuation K (algebraMap R K r) ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one]
      exact WithZero.lt_one_iff_le_exp_neg_one.mp ((valuation_lt_one_iff_mem w r).mpr hmem)
    have := hμ v w hv _ 1 hlt
    rw [hg₁ v w hv hw, Nat.cast_one, ← exp_zero, exp_le_exp] at this
    norm_num at this
  have h4a : r ∈ t₀.asIdeal := by
    by_contra hnot
    have hunit : IsUnit r := isUnit_of_forall_not_mem
      (fun w => by by_cases hw : w = t₀ <;> [exact hw ▸ hnot; exact h3 w hw]) t₀
    obtain ⟨u, hu⟩ := hunit
    have hprod : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one, map_one]
    have hle : v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ 1 :=
      hμ0 v₀ t₀ hv₀ _ (valuation_le_one t₀ _)
    have key : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ exp (-1) * 1 := by
      rw [hg₀ v₀ hv₀]
      gcongr
    rw [hprod, mul_one, ← exp_zero, exp_le_exp] at key
    norm_num at key
  have h4b : r ∉ t₀.asIdeal ^ 2 := by
    intro hmem
    have hle : t₀.valuation K (algebraMap R K r) ≤ exp (-((2 : ℕ) : ℤ)) := by
      rw [valuation_of_algebraMap]
      exact (intValuation_le_pow_iff_mem t₀ r 2).mpr hmem
    have := hμ v₀ t₀ hv₀ _ 2 hle
    rw [hg₀ v₀ hv₀, exp_le_exp] at this
    norm_num at this
  refine ⟨r, ?_⟩
  have hdvd : t₀.asIdeal ∣ Ideal.span {r} :=
    (Ideal.dvd_span_singleton).mpr h4a
  obtain ⟨J, hJ⟩ := hdvd
  suffices hJtop : J = ⊤ by rw [hJ, hJtop, Ideal.mul_top]
  by_contra hJtop
  obtain ⟨𝔪, h𝔪, hJle⟩ := Ideal.exists_le_maximal J hJtop
  have hJ0 : J ≠ ⊥ := by
    intro hJ0
    rw [hJ0, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hr0 hJ
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hJle))
  set w : HeightOneSpectrum R := ⟨𝔪, h𝔪.isPrime, h𝔪0⟩
  have hrw : r ∈ t₀.asIdeal * w.asIdeal := by
    have : t₀.asIdeal * w.asIdeal ∣ Ideal.span {r} := by
      rw [hJ]; exact mul_dvd_mul_left _ ((Ideal.dvd_iff_le).mpr hJle)
    exact (Ideal.dvd_span_singleton).mp this
  by_cases hw : w = t₀
  · apply h4b
    rw [sq, ← hw]
    nth_rewrite 1 [hw]
    exact hrw
  · exact h3 w hw (Ideal.mul_le_right hrw)

end WeilPairingND

private theorem solution {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (μ : K →+* K)
    (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R))
    (hN : ∀ w, ∃ v, N v = some w)
    (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) →
      v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ)))
    (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R)
    (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1))
    (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R,
    t₀.asIdeal = Ideal.span {r} :=
  WeilPairingND.exists_eq_span_of_eq_pullback μ N hN hμ g t₀ hg₀ hg₁ hgμ
end FunctionFieldPullback.Span


/-- **Simple zeros over a distinguished place imply that the distinguished ideal is principal.**
Let `R` be a Dedekind domain with fraction field `K`, `μ` a ring endomorphism of `K`, and `N` a
surjective partial map on the height-one primes of `R` such that, whenever `N v = some w`, for
every natural number `k` a function with valuation at most `exp (-k)` at `w` (vanishing to order
at least `k`) is sent by `μ` to a function with valuation at most `exp (-k)` at `v`. If `g = μ h`
has valuation `exp (-1)` at every place `v` with `N v = some t₀`, so that `g` has a simple zero at
each place over `t₀`, and valuation `1` at every place `v` with `N v = some w` for `w ≠ t₀`, then
the ideal `t₀` of `R` is principal. -/
theorem IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq {R : Type*}
    [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (μ : K →+* K)
    (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R))
    (hN : ∀ w, ∃ v, N v = some w)
    (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) →
      v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ)))
    (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R)
    (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1))
    (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) :
    ∃ r : R, t₀.asIdeal = Ideal.span {r} :=
  FunctionFieldPullback.Span.solution μ N hN hμ g t₀ hg₀ hg₁ hgμ

namespace FunctionFieldPullback.Exists

section PortCardSurj

namespace Deep
namespace Gen

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

private theorem nsmul_surjective_charfree [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hpos : 0 < n) :
    Function.Surjective (fun P : W.toAffine⟮K⟯ => n • P) := by
  intro Q
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · refine ⟨0, ?_⟩
    change n • (0 : W.toAffine⟮K⟯) = Point.zero
    rw [nsmul_zero]
    exact Point.zero_def
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree ≤ n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq_le (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hGdef]; exact h
  have h1n : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
  set p : K[X] := F' - C xQ * G with hpdef
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le xQ G) ?_
    rw [hFdeg]
    omega
  have hpdegne : p.degree ≠ 0 := by
    have hpos' : 0 < p.natDegree := by rw [hpdeg]; omega
    exact (natDegree_pos_iff_degree_pos.mp hpos').ne'
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hpdegne
  have hpx : p.eval x₀ = 0 := hx₀
  have hroot : F'.eval x₀ = xQ * G.eval x₀ := by
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hpx
    exact hpx
  have hGx : G.eval x₀ ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x₀ = 0 := by rw [hroot, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x₀) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, (W.baseChange K).toAffine.Equation x₀ y := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
      (C 1 * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X
        + C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
            (W.baseChange K).a₆)))
      (by rw [degree_quadratic one_ne_zero]; norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
    linear_combination hy
  have h₀ : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hy₀
  obtain ⟨x', y', h', hsmul, hx'⟩ :=
    FunctionFieldPullback.ZsmulDiv.PortCard.zsmul_some_eq_some_of_eval_ΨSq_ne_zero
      (W.baseChange K) h₀ hGx
  rw [natCast_zsmul] at hsmul
  rw [← hFdef, ← hGdef] at hx'
  have hx'Q : x' = xQ := by
    rw [hroot] at hx'
    exact mul_right_cancel₀ hGx hx'
  subst hx'Q
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQ.1 rfl with rfl | rfl
  · exact ⟨Point.some x₀ y₀ h₀, hsmul⟩
  · have hnegQ : -(Point.some x' yQ hQ : W.toAffine⟮K⟯) =
        Point.some x' ((W.baseChange K).toAffine.negY x' yQ)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
    have hprev : n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(Point.some x' yQ hQ) := by
      rw [hnegQ]
      exact hsmul
    have hsn : n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯)) :=
      neg_nsmul (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) n
    refine ⟨-(Point.some x₀ y₀ h₀), ?_⟩
    change n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) = Point.some x' yQ hQ
    rw [hsn, hprev, neg_neg]

private theorem exists_zsmul_eq [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : W.toAffine⟮K⟯) : ∃ Q : W.toAffine⟮K⟯, n • Q = P := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨Q, hQ⟩ := nsmul_surjective_charfree W (K := K) hpos P
  rcases Int.natAbs_eq n with h | h
  · exact ⟨Q, by rw [h, natCast_zsmul]; exact hQ⟩
  · exact ⟨-Q, by rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul]; exact hQ⟩

end Deep.Gen

private theorem PortCard.exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  Deep.Gen.exists_zsmul_eq (F := K) (K := K) E hn P

end PortCardSurj

private theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0) (P : E.toAffine.Point) : ∃ Q :
    E.toAffine.Point, n • Q = P :=
  PortCard.exists_zsmul_eq_of_isAlgClosed E hn P
end FunctionFieldPullback.Exists


/-- **Divisibility of points.** On an elliptic curve over an algebraically closed field, every
point is `n` times a point, for every nonzero integer `n`. -/
theorem WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  FunctionFieldPullback.Exists.solution E hn P

namespace FunctionFieldPullback.Good

open WeierstrassCurve WeierstrassCurve.Affine

section

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

private theorem not_forall_zsmul_eq_zero {n : ℤ} (hn : (n : K) ≠ 0) : ¬ ∀ S : (W⁄K).Point, n • S = 0
    := by
  intro hall
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m ∨ n = -m := ⟨n.natAbs, Int.natAbs_eq n⟩
  have hmK : (m : K) ≠ 0 := by
    intro h0
    apply hn
    rcases hm with rfl | rfl
    · rw [Int.cast_natCast, h0]
    · rw [Int.cast_neg, Int.cast_natCast, h0, neg_zero]
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hmK
  have htop : Submodule.torsionBy ℤ (W⁄K).Point m = ⊤ := by
    rw [eq_top_iff]
    intro S _
    rw [Submodule.mem_torsionBy_iff]
    rcases hm with rfl | rfl
    · exact hall S
    · have := hall S
      rwa [neg_smul, neg_eq_zero] at this
  rw [htop, Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := (W⁄K).Point)).toEquiv] at hcard
  have hm0 : m ≠ 0 := by rintro rfl; exact hmK Nat.cast_zero
  have : Finite (W⁄K).Point := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hm0)
  exact (infinite_point W K).not_finite ‹_›

end

private theorem solution {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K]
    [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) :
    WeierstrassCurve.Affine.MulGood W K n := by
  constructor
  · intro h0
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) h0
    rw [map_zsmul, map_transPull_genericPoint, map_zero, smul_add, h0, zero_add,
      ← map_zsmul] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
  · intro P hP
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) hP
    rw [map_zsmul, map_transPull_genericPoint, Point.map_baseChange, smul_add, hP, ← map_zsmul,
      add_eq_left] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
end FunctionFieldPullback.Good


/-- **Multipliers that are nonzero in `K` are admissible.** If `K` is algebraically closed, `W` is
elliptic and `(n : K) ≠ 0`, then `MulGood W K n` holds, so `mulPull W K n` is defined. -/
theorem WeierstrassCurve.Affine.zsmul_genericPoint_good {R : Type*} [Field R]
    (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K]
    [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) : WeierstrassCurve.Affine.MulGood W K n :=
  FunctionFieldPullback.Good.solution W K hn

namespace FunctionFieldPullback.Finrank

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial IntermediateField

private theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hgood : MulGood W K n) :
    FiniteDimensional (mulPull W K n hgood).fieldRange (W⁄K).FunctionField ∧ Module.finrank
    (mulPull W K n hgood).fieldRange (W⁄K).FunctionField ≤ n.natAbs ^ 2 := by
  classical
  have hEK : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  set L := (W⁄K).FunctionField with hL
  set gX := genericX W K with hXdef
  set gY := genericY W K with hYdef
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hgood.1 (zero_zsmul _)
  let f : K →ₐ[F] L := IsScalarTower.toAlgHom F K L
  have hf : (f : K →+* L) = algebraMap K L := rfl
  have hΦ : (W⁄L).Φ n = ((W⁄K).Φ n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Φ f n
  have hΨSq : (W⁄L).ΨSq n = ((W⁄K).ΨSq n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_ΨSq f n
  have hΨ₂Sq : (W⁄L).Ψ₂Sq = (W⁄K).Ψ₂Sq.map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Ψ₂Sq f
  have hγn : n • genericPoint W K ≠ 0 := hgood.1
  have hψ : ((W⁄L).ψ n).evalEval gX gY ≠ 0 := fun h0 =>
    hγn ((Point.smul_some_eq_zero_iff (W⁄L) (generic_nonsingular W K) n).mpr h0)
  have hΨX : ((W⁄L).ΨSq n).eval gX ≠ 0 := by
    rw [← WeierstrassCurve.evalEval_ψ_sq (W⁄L) (generic_equation W K) n]
    exact pow_ne_zero _ hψ
  obtain ⟨y', h', hmul⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W⁄L) (generic_nonsingular W K) hψ
  have hxn : mulPull W K n hgood gX = ((W⁄L).Φ n).eval gX / ((W⁄L).ΨSq n).eval gX := by
    rw [hXdef, mulPull_genericX' W K hgood]
    change (n • Point.some _ _ (generic_nonsingular W K)).xc = _
    rw [hmul, Point.xc_some]
  set A : L := (W⁄L).a₁ * gX + (W⁄L).a₃ with hA
  set B : L := -(gX ^ 3 + (W⁄L).a₂ * gX ^ 2 + (W⁄L).a₄ * gX + (W⁄L).a₆) with hB
  have hcoef : ∀ a : F, (algebraMap F L a) ∈ K⟮gX⟯ := fun a => by
    rw [IsScalarTower.algebraMap_apply F K L]
    exact IntermediateField.algebraMap_mem _ _
  have ha₁ : (W⁄L).a₁ = algebraMap F L W.a₁ := rfl
  have ha₂ : (W⁄L).a₂ = algebraMap F L W.a₂ := rfl
  have ha₃ : (W⁄L).a₃ = algebraMap F L W.a₃ := rfl
  have ha₄ : (W⁄L).a₄ = algebraMap F L W.a₄ := rfl
  have ha₆ : (W⁄L).a₆ = algebraMap F L W.a₆ := rfl
  have hXKX : gX ∈ K⟮gX⟯ := mem_adjoin_simple_self K gX
  have hAmem : A ∈ K⟮gX⟯ := by
    rw [hA, ha₁, ha₃]
    exact add_mem (mul_mem (hcoef _) hXKX) (hcoef _)
  have hBmem : B ∈ K⟮gX⟯ := by
    rw [hB, ha₂, ha₄, ha₆]
    refine neg_mem (add_mem (add_mem (add_mem (pow_mem hXKX 3) (mul_mem (hcoef _) (pow_mem hXKX 2)))
      (mul_mem (hcoef _) hXKX)) (hcoef _))
  have hYq : gY ^ 2 + A * gY + B = 0 := by
    have h := (equation_iff _ _).mp (generic_equation W K)
    rw [hA, hB]
    linear_combination h
  have hιX : (negEquiv W K : L →ₐ[K] L) gX = gX := negEquiv_genericX W K
  have hιY' : (negEquiv W K : L →ₐ[K] L) gY = -gY - A := by
    change negEquiv W K (genericY W K) = _
    rw [negEquiv_genericY, WeierstrassCurve.Affine.negY, hA]
    ring
  have hιY : ((negEquiv W K : L →ₐ[K] L) gY) ^ 2 + A * (negEquiv W K : L →ₐ[K] L) gY + B = 0 := by
    rw [hιY']
    linear_combination hYq
  have hιμ : (negEquiv W K : L →ₐ[K] L) (mulPull W K n hgood gY) ≠ mulPull W K n hgood gY := by
    intro heq
    change negEquiv W K (mulPull W K n hgood (genericY W K)) =
      mulPull W K n hgood (genericY W K) at heq
    rw [negEquiv_mulPull_genericY' W K hgood, mulPull_genericY' W K hgood] at heq
    have hP := Point.eq_some_xc_yc hγn
    have h2 : (2 : ℕ) • (n • genericPoint W K) = 0 := by
      rw [two_nsmul, add_eq_zero_iff_eq_neg]
      conv_rhs => rw [hP, Point.neg_some]
      conv_lhs => rw [hP]
      congr 1
      exact heq.symm
    rw [hP, (WeierstrassCurve.Affine.Ψ₂Sq_eval_eq_zero_iff_two_smul _).symm, hΨ₂Sq,
      eval_map_algebraMap] at h2
    apply not_isIntegral_xc_of_ne_baseChange (n • genericPoint W K) hgood.1 hgood.2
    exact IsAlgebraic.isIntegral
        ⟨(W⁄K).Ψ₂Sq, WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic (W⁄K), h2⟩
  have hgen : IntermediateField.adjoin K {gX, gY} = ⊤ := FunctionField.adjoin_X_Y_eq_top (W⁄K)
  have key := IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top gX gY hgen A B hAmem
      hBmem hYq (mulPull W K n hgood)
    (negEquiv W K : L →ₐ[K] L) hιX hιY hιμ ((W⁄K).Φ n) ((W⁄K).ΨSq n)
    (d := n.natAbs ^ 2) (pow_pos (Int.natAbs_pos.mpr hn0) 2) ?_ ?_
  · exact key
  · rw [← eval_map_algebraMap, ← eval_map_algebraMap, ← hΦ, ← hΨSq, hxn, div_mul_cancel₀ _ hΨX]
  · intro M c
    rw [← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq]
    exact WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq _ n c
end FunctionFieldPullback.Finrank


/-- **Degree of the multiplication pullback.** Let `W` be an elliptic curve over `F` and `K` an
algebraically closed field over `F`. For `hgood : MulGood W K n`, the function field of `W⁄K` is
finite over the image of `mulPull W K n hgood`, of degree at most `n.natAbs ^ 2`. -/
theorem WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le {F K : Type*} [Field F] [Field K]
    [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ}
    (hgood : WeierstrassCurve.Affine.MulGood W K n) :
    FiniteDimensional (WeierstrassCurve.Affine.mulPull W K n hgood).fieldRange
        (W⁄K).FunctionField ∧
      Module.finrank (WeierstrassCurve.Affine.mulPull W K n hgood).fieldRange
        (W⁄K).FunctionField ≤ n.natAbs ^ 2 :=
  FunctionFieldPullback.Finrank.solution W hgood

namespace FunctionFieldPullback.Main

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace WeilND

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

private lemma placeOf_congr {P Q : (W⁄K).Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P = Q) :
    placeOf W K P hP = placeOf W K Q hQ := by subst h; rfl

end WeilND

private theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
    {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0)
      (h : (W⁄K).FunctionField) (k : ℕ), (placeOf W K ((n : ℤ) • P) hnP).valuation
      (W⁄K).FunctionField h ≤ WithZero.exp (-(k : ℤ)) → (placeOf W K P hP).valuation
      (W⁄K).FunctionField (mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 → (placeOf W K P hP).valuation
      (W⁄K).FunctionField g = if (n : ℤ) • P = T then WithZero.exp (-1) else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → transEquiv W K S g = g) : T = 0 := by
  classical
  by_contra hT0
  have hn0 : (n : ℤ) ≠ 0 := by
    have : n ≠ 0 := fun h => hnK (by rw [h, Nat.cast_zero])
    exact_mod_cast this
  have hnK' : ((n : ℤ) : K) ≠ 0 := by exact_mod_cast hnK
  have hEK : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hgood : MulGood W K (n : ℤ) := WeierstrassCurve.Affine.zsmul_genericPoint_good W K hnK'
  obtain ⟨hfd, hdeg⟩ := WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le (K := K) W hgood
  rw [Int.natAbs_natCast] at hdeg
  have := hfd
  have hsurj : ∀ P : (W⁄K).Point, ∃ Q : (W⁄K).Point, (n : ℤ) • Q = P := fun P =>
    WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed (W⁄K) hn0 P
  let φ : Multiplicative (W⁄K).Point →* ((W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField) :=
    { toFun := fun S => transEquiv W K (Multiplicative.toAdd S)
      map_one' := by
        change transEquiv W K 0 = 1
        rw [transEquiv_zero]; rfl
      map_mul' := fun S S' => by
        change transEquiv W K (Multiplicative.toAdd S + Multiplicative.toAdd S') = _
        rw [transEquiv_add]; rfl }
  have hφ : Function.Injective φ := fun S S' h =>
    Multiplicative.toAdd.injective (transEquiv_injective W K h)
  let En : Subgroup (Multiplicative (W⁄K).Point) :=
    AddSubgroup.toSubgroup (Submodule.torsionBy ℤ (W⁄K).Point (n : ℤ)).toAddSubgroup
  have hmemEn : ∀ S, S ∈ En ↔ (n : ℤ) • Multiplicative.toAdd S = 0 := fun S => by
    change Multiplicative.toAdd S ∈ (Submodule.torsionBy ℤ (W⁄K).Point (n : ℤ)).toAddSubgroup ↔ _
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
  let H : Subgroup ((W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField) := En.map φ
  have hmemH : ∀ σ, σ ∈ H ↔ ∃ S : (W⁄K).Point, (n : ℤ) • S = 0 ∧ transEquiv W K S = σ := by
    intro σ
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨Multiplicative.toAdd S, (hmemEn S).mp hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨Multiplicative.ofAdd S, (hmemEn _).mpr hS, rfl⟩
  have hcardEn : Nat.card En = n ^ 2 := by
    rw [← WeierstrassCurve.card_torsion_of_isAlgClosed W hnK]
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun S =>
      (hmemEn S).trans (Submodule.mem_torsionBy_iff (n : ℤ) (Multiplicative.toAdd S)).symm)
  have hcardH : Nat.card H = n ^ 2 := by
    rw [← hcardEn]
    exact Subgroup.card_map_of_injective hφ
  have : Finite H := Nat.finite_of_card_ne_zero
      (by rw [hcardH]; exact pow_ne_zero _ (by exact_mod_cast hn0))
  have : Fintype H := Fintype.ofFinite H
  have hfix : Module.finrank (IntermediateField.fixedField H) (W⁄K).FunctionField = n ^ 2 := by
    rw [show Module.finrank (IntermediateField.fixedField H) (W⁄K).FunctionField =
        Module.finrank (FixedPoints.subfield H (W⁄K).FunctionField) (W⁄K).FunctionField from rfl,
      FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, hcardH]
  have hM : (mulPull W K (n : ℤ) hgood).fieldRange ≤ IntermediateField.fixedField H := by
    rintro x ⟨h, rfl⟩
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨S, hS, rfl⟩ := (hmemH σ).mp hσ
    exact transEquiv_mulPull' W K hgood hS h
  have hEq : (mulPull W K (n : ℤ) hgood).fieldRange = IntermediateField.fixedField H :=
    IntermediateField.eq_of_le_of_finrank_le' hM (by rw [hfix]; exact hdeg)
  have hgM : g ∈ (mulPull W K (n : ℤ) hgood).fieldRange := by
    rw [hEq, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨S, hS, rfl⟩ := (hmemH σ).mp hσ
    exact hinv S hS
  obtain ⟨h, hh⟩ := hgM
  let pt : HeightOneSpectrum (W⁄K).CoordinateRing → (W⁄K).Point := fun v =>
    Classical.choose (placeOf_surjective W K v)
  have hpt0 : ∀ v, pt v ≠ 0 := fun v => Classical.choose
      (Classical.choose_spec (placeOf_surjective W K v))
  have hptv : ∀ v, placeOf W K (pt v) (hpt0 v) = v := fun v =>
    Classical.choose_spec (Classical.choose_spec (placeOf_surjective W K v))
  let N : HeightOneSpectrum (W⁄K).CoordinateRing → Option (HeightOneSpectrum (W⁄K).CoordinateRing)
      :=
    fun v => if hv : (n : ℤ) • pt v = 0 then none else Option.some (placeOf W K ((n : ℤ) • pt v) hv)
  have hNsome : ∀ v w, N v = Option.some w → ∃ hv : (n : ℤ) • pt v ≠ 0, placeOf W K ((n : ℤ) • pt v)
      hv = w := by
    intro v w hvw
    by_cases hv : (n : ℤ) • pt v = 0
    · simp only [N, hv, dite_true] at hvw; exact absurd hvw (by simp)
    · simp only [N, hv, dite_false, Option.some.injEq] at hvw
      exact ⟨hv, hvw⟩
  have hpt_of_place : ∀ {P : (W⁄K).Point} (hP : P ≠ 0), pt (placeOf W K P hP) = P := fun hP =>
    placeOf_injective W K _ _ (hptv _)
  have hN : ∀ w, ∃ v, N v = Option.some w := by
    intro w
    obtain ⟨U, hU, rfl⟩ := placeOf_surjective W K w
    obtain ⟨Q, hQ⟩ := hsurj U
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hU (by rw [← hQ, smul_zero])
    refine ⟨placeOf W K Q hQ0, ?_⟩
    have hv : (n : ℤ) • pt (placeOf W K Q hQ0) ≠ 0 := by rw [hpt_of_place]; rwa [hQ]
    simp only [N, hv, dite_false, Option.some.injEq]
    exact WeilND.placeOf_congr W K _ _ (by rw [hpt_of_place, hQ])
  have key := IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq
      (R := (W⁄K).CoordinateRing) (K := (W⁄K).FunctionField)
    (mulPull W K (n : ℤ) hgood : (W⁄K).FunctionField →+* (W⁄K).FunctionField) N hN ?_ g
        (placeOf W K T hT0) ?_ ?_ ⟨h, hh⟩
  rotate_left
  · intro v w hvw x k hx
    obtain ⟨hv, rfl⟩ := hNsome v w hvw
    rw [← hptv v]
    exact hpull hgood (pt v) (hpt0 v) hv x k hx
  · intro v hv
    obtain ⟨hv', hw⟩ := hNsome v _ hv
    have hPT : (n : ℤ) • pt v = T := placeOf_injective W K _ _ hw
    rw [← hptv v, hg (pt v) (hpt0 v) hv', ite_eq_left hPT]
  · intro v w hvw hw
    obtain ⟨hv', rfl⟩ := hNsome v w hvw
    have hPT : (n : ℤ) • pt v ≠ T := fun h' => hw (WeilND.placeOf_congr W K _ _ h')
    rw [← hptv v, hg (pt v) (hpt0 v) hv', ite_eq_right hPT]
  obtain ⟨r, hr⟩ := key
  have hr0 : r ≠ 0 := by
    intro h0
    apply (placeOf W K T hT0).ne_bot
    rw [hr, h0, Ideal.span_singleton_eq_bot]
  have hTs := Point.eq_some_xc_yc hT0
  have hcls : Point.toClass T = 0 := by
    rw [hTs, Point.toClass_some]
    exact (ClassGroup.mk_eq_one_of_coe_ideal (by rfl)).mpr ⟨r, hr0, hr⟩
  exact hT0 ((Point.toClass_eq_zero T).mp hcls)
end FunctionFieldPullback.Main


/-- **A translation-invariant function with simple zeros over `T` forces `T = 0`.** Let `W` be an
elliptic curve over `F`, let `K` be an algebraically closed field over `F` such that the
coordinate ring of `W⁄K` is a Dedekind domain, and let `n` be a natural number with
`(n : K) ≠ 0`. Assume `hpull`: for every natural number `k` and every affine point `P` with
`n • P ≠ 0`, if a function has valuation at most `exp (-k)` at `n • P` (vanishes to order at least
`k` there), then its pullback by `mulPull` has valuation at most `exp (-k)` at `P`. Let `g` be a
function on `W⁄K` that is fixed by translation by every `n`-torsion point and that, at every affine
point `P` with `n • P ≠ 0`, has a simple zero (valuation `exp (-1)`) when `n • P = T` and valuation
`1` otherwise. Then `T = 0`. -/
theorem WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq {F K : Type*} [Field F] [Field K]
    [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : WeierstrassCurve.Affine.MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0)
      (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ),
      (WeierstrassCurve.Affine.placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
          WithZero.exp (-(k : ℤ)) →
        (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField
            (WeierstrassCurve.Affine.mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp (-1) else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → WeierstrassCurve.Affine.transEquiv W K S g = g) :
    T = 0 :=
  FunctionFieldPullback.Main.solution W hnK hpull g hg hinv

/-- **A translation-invariant function with simple poles over `T` forces `T = 0`.** Let `W` be an
elliptic curve over `F`, let `K` be an algebraically closed field over `F` such that the
coordinate ring of `W⁄K` is a Dedekind domain, and let `n` be a natural number with
`(n : K) ≠ 0`. Assume `hpull`: for every natural number `k` and every affine point `P` with
`n • P ≠ 0`, if a function has valuation at most `exp (-k)` at `n • P` (vanishes to order at least
`k` there), then its pullback by `mulPull` has valuation at most `exp (-k)` at `P`. Let `g` be a
function on `W⁄K` that is fixed by translation by every `n`-torsion point and that, at every affine
point `P` with `n • P ≠ 0`, has a simple pole (valuation `exp 1`) when `n • P = T` and valuation
`1` otherwise. Then `T = 0`. -/
theorem WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq_of_pole {F K : Type*} [Field F]
    [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : WeierstrassCurve.Affine.MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0)
      (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ),
      (WeierstrassCurve.Affine.placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
          WithZero.exp (-(k : ℤ)) →
        (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField
            (WeierstrassCurve.Affine.mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp 1 else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → WeierstrassCurve.Affine.transEquiv W K S g = g) :
    T = 0 := by
  refine WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq W hnK hpull g⁻¹
    (fun P hP hnP => ?_) (fun S hS => ?_)
  · rw [map_inv₀, hg P hP hnP]
    split_ifs
    · exact (WithZero.exp_neg 1).symm
    · exact inv_one
  · rw [map_inv₀, hinv S hS]

end
