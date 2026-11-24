/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_algHom_adicEval_forall_comp_eq_of_specialFibre_
coordinates.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_algHom_adicEval_forall_comp_eq_of_specialFibre_
coordinates.lean`
(https://github.com/anthropics/fermats-last-theorem), together with the
`adicEval` construction of `Definitions/Def_MvFormalGroup_PointsV2.lean`:
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

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.AdicCompletion.FiniteFree
import MathlibExt.RingTheory.MvPowerSeries.VariableIdealPower

/-!
# Power series coordinates on a tower with prescribed special fibres

`MvPowerSeries.adicEval J x f` evaluates a multivariate power series `f` over `R` at a point
`x` of an `R`-algebra `S`, using the `J`-adic topology on `S`. If `S` is `J`-adically complete
and every coordinate of `x` lies in the radical of `J`, this is an `R`-algebra homomorphism
(`MvPowerSeries.adicEvalAlgHom`) sending `X s` to `x s`.

The main theorem `MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates`
takes a tower `⋯ → R₀ 2 → R₀ 1 → R₀ 0` of finite free algebras over a `p`-adically complete
ring `𝓞` with residue ring `ZMod p`, with compatible coordinates `x v` in the radical of `(p)`.
If each special-fibre evaluation `MvPolynomial σ (ZMod p) → ZMod p ⊗ R₀ v` at the coordinates
is surjective and the kernels are cofinal in the powers of the ideal of the variables, then the
evaluations `MvPowerSeries σ 𝓞 → R₀ v` are compatible surjections, jointly injective, and
jointly surjective onto compatible families.
-/

universe u v w

open MvPowerSeries Function
open scoped TensorProduct

@[expose] public section

section AdicEval

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {S' : Type*} [CommRing S'] [Algebra R S'] {σ : Type*}

namespace MvPowerSeries

/-- Evaluation of a multivariate power series `f` over `R` at `x : σ → S`, computed in the
`J`-adic topology of `S` (with the discrete topology on `R`). It agrees with polynomial
evaluation on polynomials (`MvPowerSeries.adicEval_coe`). -/
noncomputable def adicEval (J : Ideal S) (x : σ → S) (f : MvPowerSeries σ R) : S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  MvPowerSeries.eval₂ (algebraMap R S) x f

end MvPowerSeries

namespace Ideal

/-- An element of the radical of `J` is topologically nilpotent for the `J`-adic topology. -/
theorem isTopologicallyNilpotent_of_mem_radical (J : Ideal S) {a : S}
    (ha : a ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    IsTopologicallyNilpotent a := by
  let : TopologicalSpace S := J.adicTopology
  obtain ⟨k, hk⟩ := ha
  change Filter.Tendsto (a ^ ·) Filter.atTop (nhds 0)
  rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
  rw [pow_add, pow_mul]
  exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))

end Ideal

namespace MvPowerSeries

/-- Coordinates in the radical of `J` can be substituted into power series over finitely many
variables, for the `J`-adic topology. -/
theorem hasEval_of_mem_radical [Finite σ] (J : Ideal S) {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace S := J.adicTopology
    MvPowerSeries.HasEval x := by
  let : TopologicalSpace S := J.adicTopology
  refine ⟨fun s => Ideal.isTopologicallyNilpotent_of_mem_radical J (hx s), ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

theorem adicEval_coe (J : Ideal S) (x : σ → S) (p : MvPolynomial σ R) :
    adicEval J x (p : MvPowerSeries σ R) = MvPolynomial.aeval x p := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  rw [MvPolynomial.aeval_def]
  exact MvPowerSeries.eval₂_coe (algebraMap R S) x p

theorem adicEval_X (J : Ideal S) (x : σ → S) (s : σ) :
    adicEval J x (X s : MvPowerSeries σ R) = x s := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  exact MvPowerSeries.eval₂_X (algebraMap R S) x s

/-- For a `J`-adically complete `S` and coordinates in the radical of `J`, `adicEval J x` is
an `R`-algebra homomorphism (`MvPowerSeries.coe_adicEvalAlgHom`). -/
noncomputable def adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : MvPowerSeries σ R →ₐ[R] S :=
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  MvPowerSeries.aeval (hasEval_of_mem_radical J hx)

theorem coe_adicEvalAlgHom [Finite σ] (J : Ideal S) [IsAdicComplete J S] {x : σ → S}
    (hx : ∀ s, x s ∈ J.radical) : ⇑(adicEvalAlgHom (R := R) J hx) = adicEval J x := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  have : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  have : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  have : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  funext f
  exact congrFun (MvPowerSeries.coe_aeval (hasEval_of_mem_radical J hx)) f

/-- `adicEval` commutes with an `R`-algebra map `φ : S → S'` between adically complete rings
that sends the finitely generated ideal `J` into the radical of `J'`. -/
theorem map_adicEval [Finite σ] (J : Ideal S) [IsAdicComplete J S] (J' : Ideal S')
    [IsAdicComplete J' S'] (φ : S →ₐ[R] S') (hJ : J.FG) (hφ : ∀ s ∈ J, φ s ∈ J'.radical)
    {x : σ → S} (hx : ∀ s, x s ∈ J.radical) (f : MvPowerSeries σ R) :
    φ (adicEval J x f) = adicEval J' (fun s => φ (x s)) f := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  let : WithIdeal S' := ⟨J'⟩
  have : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  have : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  have : CompleteSpace S' :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J' from rfl)).mp ‹IsAdicComplete J' S'›).1
  have : T2Space S' :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J' from rfl)).mp ‹IsAdicComplete J' S'›).2
  have hle : J.map (φ : S →+* S') ≤ J'.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact hφ s hs
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (hJ.map _)
  have hcont : Continuous (φ : S →+* S') := by
    apply continuous_of_continuousAt_zero (φ : S →+* S')
    rw [ContinuousAt, map_zero,
      (J.hasBasis_nhds_zero_adic).tendsto_iff (J'.hasBasis_nhds_zero_adic)]
    intro n _
    refine ⟨m * n, trivial, fun s hs => ?_⟩
    have hpow : (J ^ (m * n)).map (φ : S →+* S') ≤ J' ^ n := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_right_mono hm n
    exact SetLike.mem_coe.mpr (hpow (Ideal.mem_map_of_mem _ (SetLike.mem_coe.mp hs)))
  have key := congrFun (MvPowerSeries.comp_eval₂ (φ := algebraMap R S) (a := x)
    continuous_of_discreteTopology (hasEval_of_mem_radical J hx) hcont) f
  rw [AlgHom.comp_algebraMap] at key
  exact key

end MvPowerSeries

end AdicEval

end

namespace MvPowerSeries.SpecialFibreCoordinates

section Reduction

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)] (T : Type v) [CommRing T]
  [Algebra 𝓞 T]

private noncomputable abbrev red : T →ₐ[𝓞] ZMod p ⊗[𝓞] T := Algebra.TensorProduct.includeRight

variable {𝓞 p T}

private theorem red_apply (a : T) : red 𝓞 p T a = (1 : ZMod p) ⊗ₜ[𝓞] a := rfl

private theorem natCast_eq_zero : (p : ZMod p ⊗[𝓞] T) = 0 := by
  rw [Algebra.TensorProduct.natCast_def, ZMod.natCast_self, TensorProduct.zero_tmul]

private theorem red_natCast_mul (a : T) : red 𝓞 p T ((p : T) * a) = 0 := by
  rw [map_mul, map_natCast, natCast_eq_zero, zero_mul]

private theorem ker_red (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (red 𝓞 p T : T →ₐ[𝓞] ZMod p ⊗[𝓞] T) = Ideal.span {(p : T)} := by
  apply le_antisymm
  · set J : Ideal T := Ideal.span {(p : T)} with hJ
    have hle : RingHom.ker (algebraMap 𝓞 (ZMod p)) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 T)) := by
      intro o ho
      rw [hker] at ho
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    let κ₀ : ZMod p →+* T ⧸ J := (algebraMap 𝓞 (ZMod p)).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 (ZMod p) o) = Ideal.Quotient.mk J (algebraMap 𝓞 T o) :=
      fun o =>
      (algebraMap 𝓞 (ZMod p)).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : ZMod p →ₐ[𝓞] T ⧸ J := { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
    let Ψ : ZMod p ⊗[𝓞] T →ₐ[𝓞] T ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro a ha
    rw [RingHom.mem_ker] at ha
    have h1 : Ψ (red 𝓞 p T a) = Ideal.Quotient.mk J a := by
      rw [red_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    rw [show red 𝓞 p T a = 0 from ha, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have := red_natCast_mul (𝓞 := 𝓞) (p := p) (1 : T)
    rwa [mul_one] at this

private theorem red_eq_red_iff (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (a b : T) :
    red 𝓞 p T a = red 𝓞 p T b ↔ a - b ∈ Ideal.span {(p : T)} := by
  rw [← ker_red hk hker, RingHom.mem_ker, map_sub, sub_eq_zero]

end Reduction

section Eval

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)

variable (𝓞) in
private noncomputable def evalAt (v : ℕ) : MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v :=
  haveI : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  MvPowerSeries.adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : R₀ v)}) (hxr v)

private theorem evalAt_apply (v : ℕ) (G : MvPowerSeries σ 𝓞) :
    evalAt 𝓞 p R₀ x hxr v G = MvPowerSeries.adicEval (Ideal.span {(p : R₀ v)}) (x v) G := by
  have : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  exact congrFun (MvPowerSeries.coe_adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : R₀ v)}) (hxr v)) G

private theorem evalAt_X (v : ℕ) (i : σ) :
    evalAt 𝓞 p R₀ x hxr v (X i : MvPowerSeries σ 𝓞) = x v i := by
  rw [evalAt_apply, MvPowerSeries.adicEval_X]

private theorem evalAt_coe (v : ℕ) (P : MvPolynomial σ 𝓞) :
    evalAt 𝓞 p R₀ x hxr v (P : MvPowerSeries σ 𝓞) = MvPolynomial.aeval (x v) P := by
  rw [evalAt_apply, MvPowerSeries.adicEval_coe]

private theorem comp_evalAt (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
    (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
    (v : ℕ) : (t v).comp (evalAt 𝓞 p R₀ x hxr (v + 1)) = evalAt 𝓞 p R₀ x hxr v := by
  have : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  have : IsAdicComplete (Ideal.span {(p : R₀ (v + 1))}) (R₀ (v + 1)) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ (v + 1))
  apply AlgHom.ext
  intro G
  rw [AlgHom.comp_apply, evalAt_apply, evalAt_apply,
    MvPowerSeries.map_adicEval (R := 𝓞) (Ideal.span {(p : R₀ (v + 1))}) (Ideal.span {(p : R₀ v)})
      (t v) (Submodule.fg_span_singleton _) ?_ (hxr (v + 1)) G]
  · congr 1
    funext i
    exact hxt v i
  · intro s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine Ideal.le_radical ?_
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Eval

section Surj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))

include hxred in
private theorem red_evalAt_coe (v : ℕ) (P : MvPolynomial σ 𝓞) :
    red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (P : MvPowerSeries σ 𝓞)) =
      πbar v (MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P) := by
  rw [evalAt_coe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hπ : πbar v = MvPolynomial.aeval (fun i => πbar v (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i =>
      (MvPolynomial.aeval_X (fun i => πbar v (MvPolynomial.X i)) i).symm
  rw [hπ, MvPolynomial.aeval_map_algebraMap]
  congr 2
  funext i
  exact hxred v i

end Surj

section SurjInj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))

include hxred hk hker hπs in
private theorem evalAt_surjective (v : ℕ) : Surjective (evalAt 𝓞 p R₀ x hxr v) := by
  let N : Submodule 𝓞 (R₀ v) := LinearMap.range (evalAt 𝓞 p R₀ x hxr v).toLinearMap
  have hN : (⊤ : Submodule 𝓞 (R₀ v)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : 𝓞)})
      Module.Finite.fg_top
      (IsAdicComplete.le_jacobson_bot _) ?_
    intro m _
    obtain ⟨Q, hQ⟩ := hπs v (red 𝓞 p (R₀ v) m)
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (algebraMap 𝓞 (ZMod p)) hk Q
    have hdiff : m - evalAt 𝓞 p R₀ x hxr v ↑P ∈ Ideal.span {(p : R₀ v)} := by
      rw [← red_eq_red_iff hk hker, red_evalAt_coe p R₀ x hxr πbar hxred, hQ]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdiff
    have hm : m = evalAt 𝓞 p R₀ x hxr v ↑P + (p : 𝓞) • c := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-1 : R₀ v) * hc
    rw [hm]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  intro m
  obtain ⟨G, hG⟩ := hN (Submodule.mem_top (x := m))
  exact ⟨G, hG⟩

omit [Fact p.Prime] in
private theorem coeff_eq_zero_of_mem_pow_span_X {k : Type*} [CommRing k] {σ : Type*} :
    ∀ (K : ℕ) {φ : MvPolynomial σ k},
      φ ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ K →
      ∀ m : σ →₀ ℕ, m.degree < K → φ.coeff m = 0
  | 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | K + 1, φ, hφ, m₀, hm₀ => by
    classical
    rw [pow_succ] at hφ
    refine Submodule.smul_induction_on
      (p := fun ψ => ∀ m : σ →₀ ℕ, m.degree < K + 1 → ψ.coeff m = 0) hφ ?_ ?_ m₀ hm₀
    · intro a ha b hb m hm
      rw [smul_eq_mul, MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨m₁, m₂⟩ hmm
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmm
      by_cases h₁ : m₁.degree < K
      · rw [coeff_eq_zero_of_mem_pow_span_X K ha m₁ h₁, zero_mul]
      · have hdeg : m₁.degree + m₂.degree = m.degree := by rw [← map_add, hmm]
        have h₂ : m₂ = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
        subst h₂
        have hb0 : b.coeff 0 = 0 := by
          rw [← Set.image_univ] at hb
          rw [← MvPolynomial.notMem_support_iff]
          intro h0
          obtain ⟨i, -, hi⟩ := (MvPolynomial.mem_ideal_span_X_image.1 hb) 0 h0
          exact hi rfl
        rw [hb0, mul_zero]
    · intro a b ha hb m hm
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha m hm, hb m hm, add_zero]

include hxred hker hπs in
private theorem coeff_mem_span_of_evalAt_eq_zero {K : ℕ} {v : ℕ}
    (hv : RingHom.ker (πbar v) ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ K)
    {G : MvPowerSeries σ 𝓞} (hG : evalAt 𝓞 p R₀ x hxr v G = 0)
    (m : σ →₀ ℕ) (hm : m.degree < K) : MvPowerSeries.coeff m G ∈ Ideal.span {(p : 𝓞)} := by
  classical
  set box : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => K with hbox
  set P : MvPolynomial σ 𝓞 := MvPowerSeries.trunc' 𝓞 box G with hP
  set H : MvPowerSeries σ 𝓞 := G - ↑P with hH
  have hmbox : ∀ m' : σ →₀ ℕ, m'.degree < K → m' ≤ box := by
    intro m' hm' i
    rw [hbox, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finsupp.le_degree i m').trans hm'.le
  have hHcoeff : ∀ m' : σ →₀ ℕ, m'.degree < K → MvPowerSeries.coeff m' H = 0 := by
    intro m' hm'
    rw [hH, map_sub, MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_trunc',
      ite_eq_left (hmbox m' hm'),
      sub_self]
  have hHmem := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero K H hHcoeff
  set 𝔛 : Ideal (MvPowerSeries σ 𝓞) :=
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) with h𝔛
  set 𝔛ₚ : Ideal (MvPolynomial σ (ZMod p)) :=
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) with h𝔛ₚ
  have hπH : evalAt 𝓞 p R₀ x hxr v H ∈ (Ideal.span (Set.range (x v))) ^ K := by
    have h1 : evalAt 𝓞 p R₀ x hxr v H ∈ Ideal.map (evalAt 𝓞 p R₀ x hxr v) (𝔛 ^ K) :=
      Ideal.mem_map_of_mem _ hHmem
    rw [Ideal.map_pow, h𝔛, Ideal.map_span, ← Set.range_comp] at h1
    have hcomp : (⇑(evalAt 𝓞 p R₀ x hxr v) ∘ (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) = x v :=
      funext fun i => evalAt_X p R₀ x hxr v i
    rwa [hcomp] at h1
  have hred : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v ↑P) ∈ Ideal.map (πbar v) (𝔛ₚ ^ K) := by
    have hPH : evalAt 𝓞 p R₀ x hxr v ↑P = - evalAt 𝓞 p R₀ x hxr v H := by
      rw [hH, map_sub, hG, zero_sub, neg_neg]
    rw [hPH, map_neg, Ideal.neg_mem_iff]
    have h2 : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v H) ∈
        Ideal.map (red 𝓞 p (R₀ v)) ((Ideal.span (Set.range (x v))) ^ K) :=
      Ideal.mem_map_of_mem _ hπH
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
    rw [Ideal.map_pow, h𝔛ₚ, Ideal.map_span, ← Set.range_comp]
    have hcomp : (⇑(red 𝓞 p (R₀ v)) ∘ x v) =
        (⇑(πbar v) ∘ (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) :=
      funext fun i => hxred v i
    rwa [hcomp] at h2
  rw [red_evalAt_coe p R₀ x hxr πbar hxred] at hred
  have hPbar : MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P ∈ 𝔛ₚ ^ K := by
    have h3 := Ideal.mem_comap.2 hred
    rw [Ideal.comap_map_of_surjective _ (hπs v)] at h3
    have h4 : 𝔛ₚ ^ K ⊔ Ideal.comap (πbar v) ⊥ ≤ 𝔛ₚ ^ K := sup_le le_rfl hv
    exact h4 h3
  have h5 := coeff_eq_zero_of_mem_pow_span_X K hPbar m hm
  rw [MvPolynomial.coeff_map, ← RingHom.mem_ker, hker] at h5
  have h6 : P.coeff m = MvPowerSeries.coeff m G := by
    rw [hP, MvPowerSeries.coeff_trunc', ite_eq_left (hmbox m hm)]
  rwa [h6] at h5

end SurjInj

section Inj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))
  (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  (hπk : ∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N)

omit [Fact p.Prime] [Algebra 𝓞 (ZMod p)] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] in
private theorem natCast_mem_nonZeroDivisors (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (T : Type v) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] :
    (p : T) ∈ nonZeroDivisors T := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  have hy' : (p : 𝓞) • y = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]
    exact hy
  let b := Module.Free.chooseBasis 𝓞 T
  apply b.repr.injective
  rw [map_zero]
  ext i
  have hi := congrArg (fun z => b.repr z i) hy'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at hi
  rw [Finsupp.zero_apply]
  exact mem_nonZeroDivisors_iff_right.1 hp _ (by rwa [mul_comm] at hi)

include hxred hker hπs hp hπk in
private theorem exists_eq_smul_of_forall_evalAt_eq_zero {G : MvPowerSeries σ 𝓞}
    (hG : ∀ v, evalAt 𝓞 p R₀ x hxr v G = 0) :
    ∃ G' : MvPowerSeries σ 𝓞, G = (p : 𝓞) • G' ∧ ∀ v, evalAt 𝓞 p R₀ x hxr v G' = 0 := by
  have hcoeff : ∀ m : σ →₀ ℕ, MvPowerSeries.coeff m G ∈ Ideal.span {(p : 𝓞)} := by
    intro m
    obtain ⟨v, hv⟩ := hπk (m.degree + 1)
    exact coeff_mem_span_of_evalAt_eq_zero p R₀ x hxr πbar hxred hker hπs hv (hG v) m
      (Nat.lt_succ_self _)
  choose c hc using fun m => Ideal.mem_span_singleton'.1 (hcoeff m)
  let G' : MvPowerSeries σ 𝓞 := c
  have hGeq : G = (p : 𝓞) • G' := by
    ext m
    rw [MvPowerSeries.coeff_smul, mul_comm]
    exact (hc m).symm
  refine ⟨G', hGeq, fun v => ?_⟩
  have h := hG v
  rw [hGeq, map_smul, Algebra.smul_def, map_natCast] at h
  exact (mem_nonZeroDivisors_iff_right.1 (natCast_mem_nonZeroDivisors p hp (R₀ v)) _
    (by rwa [mul_comm] at h))

include hxred hker hπs hp hπk in
private theorem eq_zero_of_forall_evalAt_eq_zero {G : MvPowerSeries σ 𝓞}
    (hG : ∀ v, evalAt 𝓞 p R₀ x hxr v G = 0) : G = 0 := by
  have iter : ∀ n : ℕ, ∀ G : MvPowerSeries σ 𝓞, (∀ v, evalAt 𝓞 p R₀ x hxr v G = 0) →
      ∀ m, MvPowerSeries.coeff m G ∈ Ideal.span {(p : 𝓞) ^ n} := by
    intro n
    induction n with
    | zero =>
      intro G _ m
      rw [pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    | succ n ih =>
      intro G hG m
      obtain ⟨G', rfl, hG'⟩ := exists_eq_smul_of_forall_evalAt_eq_zero p R₀ x hxr πbar hxred hker
        hπs hp hπk hG
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (ih G' hG' m)
      rw [map_smul, smul_eq_mul, ← hc]
      exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩
  ext m
  rw [map_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞) _ fun n => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact iter n G hG m

end Inj

section Trunc

variable {R : Type*} [CommRing R] {σ : Type w} [Finite σ]

private noncomputable def truncDeg (K : ℕ) (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ (Finsupp.finite_of_degree_lt (σ := σ) K).toFinset,
    MvPolynomial.monomial m (MvPowerSeries.coeff m φ)

private theorem coeff_truncDeg (K : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    (truncDeg K φ).coeff m = if m.degree < K then MvPowerSeries.coeff m φ else 0 := by
  classical
  rw [truncDeg, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

private theorem coeff_sub_truncDeg (K : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ)
    (hm : m.degree < K) :
    MvPowerSeries.coeff m (φ - (truncDeg K φ : MvPowerSeries σ R)) = 0 := by
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncDeg, ite_eq_left hm, sub_self]

private theorem sub_truncDeg_mem (K : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncDeg K φ : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ K :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero K _ (coeff_sub_truncDeg K φ)

end Trunc

section Prelim

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]

private theorem ker_anti (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v) {σ : Type w} [Finite σ]
    (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
    (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
    {v w : ℕ} (h : v ≤ w) : RingHom.ker (πbar w) ≤ RingHom.ker (πbar v) := by
  induction h with
  | refl => exact le_rfl
  | @step w _ ih =>
    refine le_trans ?_ ih
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    rw [← hπc w P, hP, map_zero]

private theorem exists_pow_span_red_eq_bot {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
    (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical) (v : ℕ) :
    ∃ M : ℕ, Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i)) ^ M = ⊥ := by
  have hfg : (Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i))).FG :=
    ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hnil : IsNilpotent (Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i))) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hxr v i
    refine ⟨n, ?_⟩
    rw [← map_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [← hc, map_mul, map_natCast, natCast_eq_zero, mul_zero]
    exact Ideal.zero_mem _
  obtain ⟨M, hM⟩ := hnil
  exact ⟨M, hM⟩

end Prelim

section JSurj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
    Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))
  (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  (hπk : ∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N)

include hxred hπc hk hker hπs hπk hxr in
private theorem exists_sub_evalAt_mem (z : ∀ v, R₀ v) (hz : ∀ v, t v (z (v + 1)) = z v) :
    ∃ G₀ : MvPowerSeries σ 𝓞, ∀ v, z v - evalAt 𝓞 p R₀ x hxr v G₀ ∈ Ideal.span {(p : R₀ v)} := by
  classical
  have hP : ∀ v, ∃ P : MvPolynomial σ 𝓞,
      πbar v (MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P) = red 𝓞 p (R₀ v) (z v) := by
    intro v
    obtain ⟨Q, hQ⟩ := hπs v (red 𝓞 p (R₀ v) (z v))
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (algebraMap 𝓞 (ZMod p)) hk Q
    exact ⟨P, hQ⟩
  choose P hP using hP
  set Pb : ∀ v, MvPolynomial σ (ZMod p) := fun v => MvPolynomial.map (algebraMap 𝓞 (ZMod p)) (P v)
    with hPb
  have htel : ∀ {v w : ℕ}, v ≤ w → Pb w - Pb v ∈ RingHom.ker (πbar v) := by
    intro v w h
    induction h with
    | refl => rw [sub_self]; exact zero_mem _
    | @step w hvw ih =>
      have h1 : Pb (w + 1) - Pb w ∈ RingHom.ker (πbar w) := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← hπc w, hPb]
        simp only
        rw [hP (w + 1), hP w, red_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hz w,
          red_apply]
      have : Pb (w + 1) - Pb v = (Pb (w + 1) - Pb w) + (Pb w - Pb v) := by ring
      rw [this]
      exact add_mem (ker_anti p R₀ t πbar hπc hvw h1) ih
  let v₀ : ℕ → ℕ := fun N => Nat.find (hπk N)
  have hv₀ : ∀ N, RingHom.ker (πbar (v₀ N)) ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N :=
    fun N => Nat.find_spec (hπk N)
  have hv₀mono : ∀ {N N' : ℕ}, N ≤ N' → v₀ N ≤ v₀ N' := by
    intro N N' h
    exact Nat.find_mono (fun v hv => hv.trans (Ideal.pow_le_pow_right h))
  let Gb : MvPowerSeries σ (ZMod p) := fun m => (Pb (v₀ (m.degree + 1))).coeff m
  have hGb : ∀ (K w : ℕ), v₀ K ≤ w → ∀ m : σ →₀ ℕ, m.degree < K →
      (Pb w).coeff m = Gb m := by
    intro K w hw m hm
    have hu : v₀ (m.degree + 1) ≤ w := (hv₀mono hm).trans hw
    have hdiff := htel hu
    have hzero := coeff_eq_zero_of_mem_pow_span_X (m.degree + 1)
      ((hv₀ (m.degree + 1)) hdiff) m (Nat.lt_succ_self _)
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at hzero
    exact hzero
  choose g hg using fun m => hk (Gb m)
  let G₀ : MvPowerSeries σ 𝓞 := g
  refine ⟨G₀, fun v => ?_⟩
  obtain ⟨K, hK⟩ := exists_pow_span_red_eq_bot (𝓞 := 𝓞) p R₀ x hxr v
  set w := max v (v₀ K) with hw
  have h1 : z v - evalAt 𝓞 p R₀ x hxr v ↑(P w) ∈ Ideal.span {(p : R₀ v)} := by
    rw [← red_eq_red_iff hk hker, red_evalAt_coe p R₀ x hxr πbar hxred]
    have := htel (le_max_left v (v₀ K))
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    change red 𝓞 p (R₀ v) (z v) = πbar v (Pb w)
    rw [this, hP v]
  have h2 : evalAt 𝓞 p R₀ x hxr v ↑(P w) - evalAt 𝓞 p R₀ x hxr v G₀ ∈ Ideal.span {(p : R₀ v)} := by
    rw [← red_eq_red_iff hk hker, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub]
    set D : MvPowerSeries σ 𝓞 := G₀ - ↑(P w) with hD
    have hsplit : D = (truncDeg K D : MvPowerSeries σ 𝓞) +
        (D - (truncDeg K D : MvPowerSeries σ 𝓞)) := by ring
    rw [hsplit, map_add, map_add]
    have hlow : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (truncDeg K D : MvPowerSeries σ 𝓞)) = 0 := by
      rw [red_evalAt_coe p R₀ x hxr πbar hxred]
      have : MvPolynomial.map (algebraMap 𝓞 (ZMod p)) (truncDeg K D) = 0 := by
        ext m
        rw [MvPolynomial.coeff_map, coeff_truncDeg, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        split_ifs with hm
        · rw [hD, map_sub, MvPolynomial.coeff_coe, map_sub,
            show MvPowerSeries.coeff m G₀ = g m from rfl,
            hg m, ← hGb K w (le_max_right _ _) m hm, hPb]
          simp only
          rw [MvPolynomial.coeff_map, sub_self]
        · rw [map_zero]
      rw [this, map_zero]
    have hhigh :
        red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (D - (truncDeg K D : MvPowerSeries σ 𝓞))) = 0 := by
      have hmem : evalAt 𝓞 p R₀ x hxr v (D - (truncDeg K D : MvPowerSeries σ 𝓞)) ∈
          (Ideal.span (Set.range (x v))) ^ K := by
        have h1 := Ideal.mem_map_of_mem (evalAt 𝓞 p R₀ x hxr v) (sub_truncDeg_mem K D)
        rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h1
        have hcomp : (⇑(evalAt 𝓞 p R₀ x hxr v) ∘
            (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) = x v :=
          funext fun i => evalAt_X p R₀ x hxr v i
        rwa [hcomp] at h1
      have h2 := Ideal.mem_map_of_mem (red 𝓞 p (R₀ v)) hmem
      rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
      have hcomp2 : (⇑(red 𝓞 p (R₀ v)) ∘ x v) = fun i => red 𝓞 p (R₀ v) (x v i) := rfl
      rw [hcomp2, hK] at h2
      exact (Submodule.mem_bot _).1 h2
    rw [hlow, hhigh, add_zero]
  have := add_mem h1 h2
  rwa [sub_add_sub_cancel] at this

end JSurj

section Iter

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
    Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))
  (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  (hπk : ∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N)

include hxt in
omit [Fact p.Prime] [Algebra 𝓞 (ZMod p)] in
private theorem map_evalAt_succ (v : ℕ) (G : MvPowerSeries σ 𝓞) :
    t v (evalAt 𝓞 p R₀ x hxr (v + 1) G) = evalAt 𝓞 p R₀ x hxr v G := by
  have := comp_evalAt p R₀ x hxr t hxt v
  exact AlgHom.congr_fun this G

include hxt hxred hπc hk hker hπs hp hπk in
private theorem exists_step (z : ∀ v, R₀ v) (hz : ∀ v, t v (z (v + 1)) = z v) :
    ∃ (G₀ : MvPowerSeries σ 𝓞) (z' : ∀ v, R₀ v), (∀ v, t v (z' (v + 1)) = z' v) ∧
      ∀ v, z v = evalAt 𝓞 p R₀ x hxr v G₀ + (p : R₀ v) * z' v := by
  obtain ⟨G₀, hG₀⟩ := exists_sub_evalAt_mem p R₀ t x hxr πbar hxred hπc hk hker hπs hπk z hz
  choose c hc using fun v => Ideal.mem_span_singleton'.1 (hG₀ v)
  refine ⟨G₀, c, fun v => ?_, fun v => ?_⟩
  · have hreg := natCast_mem_nonZeroDivisors p hp (R₀ v)
    refine sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 hreg _ ?_)
    rw [sub_mul, hc v, ← map_natCast (t v) p, ← map_mul, hc (v + 1), map_sub, hz v,
      map_evalAt_succ p R₀ t x hxr hxt, sub_self]
  · rw [mul_comm, hc v]; ring

include hxt hxred hπc hk hker hπs hp hπk in
private theorem exists_forall_evalAt_eq (z : ∀ v, R₀ v) (hz : ∀ v, t v (z (v + 1)) = z v) :
    ∃ G : MvPowerSeries σ 𝓞, ∀ v, evalAt 𝓞 p R₀ x hxr v G = z v := by
  classical
  have hstep : ∀ s : {z : ∀ v, R₀ v // ∀ v, t v (z (v + 1)) = z v},
      ∃ (G₀ : MvPowerSeries σ 𝓞) (s' : {z : ∀ v, R₀ v // ∀ v, t v (z (v + 1)) = z v}),
        ∀ v, s.1 v = evalAt 𝓞 p R₀ x hxr v G₀ + (p : R₀ v) * s'.1 v := by
    intro s
    obtain ⟨G₀, z', hz', h⟩ :=
      exists_step p R₀ t x hxr hxt πbar hxred hπc hk hker hπs hp hπk s.1 s.2
    exact ⟨G₀, ⟨z', hz'⟩, h⟩
  choose Gs nxt hnxt using hstep
  let seq : ℕ → {z : ∀ v, R₀ v // ∀ v, t v (z (v + 1)) = z v} :=
    fun n => Nat.rec ⟨z, hz⟩ (fun _ s => nxt s) n
  have seq_succ : ∀ n, seq (n + 1) = nxt (seq n) := fun n => rfl
  let Gn : ℕ → MvPowerSeries σ 𝓞 := fun n => Gs (seq n)
  let Sn : ℕ → MvPowerSeries σ 𝓞 := fun n => ∑ k ∈ Finset.range n, (p : 𝓞) ^ k • Gn k
  have hSn : ∀ n v, z v = evalAt 𝓞 p R₀ x hxr v (Sn n) + (p : R₀ v) ^ n * (seq n).1 v := by
    intro n
    induction n with
    | zero =>
      intro v
      simp only [Sn, Finset.range_zero, Finset.sum_empty, map_zero, pow_zero, one_mul, zero_add]
      rfl
    | succ n ih =>
      intro v
      have h1 := hnxt (seq n) v
      rw [← seq_succ] at h1
      simp only [Sn] at ih ⊢
      rw [Finset.sum_range_succ, map_add, map_smul, Algebra.smul_def, map_pow, map_natCast, ih v,
        h1, pow_succ]
      ring
  have hcauchy : ∀ (m : σ →₀ ℕ) {a b : ℕ}, a ≤ b →
      MvPowerSeries.coeff m (Sn a) ≡ MvPowerSeries.coeff m (Sn b)
        [SMOD (Ideal.span {(p : 𝓞)} ^ a • ⊤ : Submodule 𝓞 𝓞)] := by
    intro m a b hab
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, ← map_sub]
    have : Sn a - Sn b = - ∑ k ∈ Finset.Ico a b, (p : 𝓞) ^ k • Gn k := by
      simp only [Sn]
      rw [← Finset.sum_range_add_sum_Ico _ hab]
      ring
    rw [this, map_neg, Ideal.neg_mem_iff, map_sum]
    refine Ideal.sum_mem _ fun k hk' => ?_
    rw [Finset.mem_Ico] at hk'
    rw [map_smul, smul_eq_mul]
    obtain ⟨j, rfl⟩ : ∃ j, k = a + j := ⟨k - a, by omega⟩
    rw [pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hprec : ∀ m : σ →₀ ℕ, ∃ L : 𝓞, ∀ n,
      MvPowerSeries.coeff m (Sn n) ≡ L [SMOD (Ideal.span {(p : 𝓞)} ^ n • ⊤ : Submodule 𝓞 𝓞)] :=
    fun m => IsPrecomplete.prec' _ (hcauchy m)
  choose L hL using hprec
  let G : MvPowerSeries σ 𝓞 := L
  have hdiv : ∀ N : ℕ, ∃ H : MvPowerSeries σ 𝓞, G - Sn N = (p : 𝓞) ^ N • H := by
    intro N
    have hc : ∀ m : σ →₀ ℕ, ∃ c : 𝓞, c * (p : 𝓞) ^ N = MvPowerSeries.coeff m (G - Sn N) := by
      intro m
      have h := (hL m N).symm
      rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] at h
      rw [map_sub]
      exact Ideal.mem_span_singleton'.1 h
    choose c hc using hc
    let H : MvPowerSeries σ 𝓞 := c
    refine ⟨H, ?_⟩
    ext m
    rw [← hc m, MvPowerSeries.coeff_smul, mul_comm]
    rfl
  refine ⟨G, fun v => ?_⟩
  have : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  symm
  refine sub_eq_zero.1
    (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R₀ v)}) (R₀ v)) _
    fun N => ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  obtain ⟨H, hH⟩ := hdiv N
  have hG : G = Sn N + (p : 𝓞) ^ N • H := by rw [← hH]; ring
  have : z v - evalAt 𝓞 p R₀ x hxr v G =
      (p : R₀ v) ^ N * ((seq N).1 v - evalAt 𝓞 p R₀ x hxr v H) := by
    conv_lhs => rw [hSn N v, hG]
    rw [map_add, map_smul, Algebra.smul_def, map_pow, map_natCast]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Iter

end MvPowerSeries.SpecialFibreCoordinates

@[expose] public section

open MvPowerSeries.SpecialFibreCoordinates in
/-- **Power series coordinates on a tower with prescribed special fibres.**

Let `𝓞` be `p`-adically complete with `p` regular and `𝓞 / (p) = ZMod p`, and let
`⋯ → R₀ 2 → R₀ 1 → R₀ 0` be a tower of finite free `𝓞`-algebras with compatible coordinates
`x v : σ → R₀ v` in the radical of `(p)`. Suppose each special-fibre evaluation
`MvPolynomial σ (ZMod p) → ZMod p ⊗[𝓞] R₀ v` at the reduced coordinates is surjective, and
for every `N` some kernel lies in the `N`th power of the ideal of the variables. Then the
`p`-adic evaluations `π v : MvPowerSeries σ 𝓞 → R₀ v` at `x v` are compatible surjective
`𝓞`-algebra maps, jointly injective, and every compatible family is hit by one series. -/
theorem MvPowerSeries.exists_algHom_adicEval_forall_comp_eq_of_specialFibre_coordinates
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
    [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
    {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N) :
    ∃ π : ∀ v, MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v,
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvPowerSeries.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  classical
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  let πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v) :=
    fun v => MvPolynomial.aeval fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i
  have hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i) := by
    intro v i
    rw [red_apply]
    exact (MvPolynomial.aeval_X (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) i).symm
  have hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v) (πbar (v + 1) P) =
        πbar v P := by
    intro v P
    rw [← AlgHom.comp_apply]
    congr 1
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply]
    simp only [πbar, MvPolynomial.aeval_X, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hxt v i]
  refine ⟨evalAt 𝓞 p R₀ x hxrad, fun v i => evalAt_X p R₀ x hxrad v i,
    fun v => evalAt_surjective p R₀ x hxrad πbar hxred hk hker hxsurj v,
    fun v => comp_evalAt p R₀ x hxrad t₀ hxt v, fun v i => ?_, fun v G => ?_,
    fun G hG => eq_zero_of_forall_evalAt_eq_zero p R₀ x hxrad πbar hxred hker hxsurj hp hxker hG,
    fun z hz => exists_forall_evalAt_eq p R₀ t₀ x hxrad hxt πbar hxred hπc hk hker hxsurj hp hxker
      z hz⟩
  · rw [evalAt_X]
    exact hxrad v i
  · rw [evalAt_apply]
    congr 1
    funext i
    exact (evalAt_X p R₀ x hxrad v i).symm

end
