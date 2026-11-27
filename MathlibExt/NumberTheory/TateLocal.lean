/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_TateLocalZeta.lean`,
`Definitions/Def_LanglandsTunnell_SchwartzBruhatSpace.lean` and
`Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`
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

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Connected
public import MathlibExt.NumberTheory.NumberField.AdelicFourier
public import MathlibExt.NumberTheory.NumberField.HeckeCharacter
public import MathlibExt.NumberTheory.NumberField.HigherUnits

/-!
# Local Tate theory

For a locally compact field `K`, this file defines the modulus `modulus a` (the factor by which
multiplication by `a` scales Haar measure), the Schwartz--Bruhat test functions, the local
Fourier transform `tateFourier`, the measure `mulMeasure μ = μ(dx) / modulus x` on `{0}ᶜ`
attached to an additive Haar measure `μ`, and the local zeta integrals `localZeta μ f χ s`, in
which a character `χ` of `Kˣ` is extended by zero to `K` as Mathlib's `MulChar.ofUnitHom χ`.
When singletons are measurable, as on a local field, `mulMeasure μ` gives `{0}` mass zero
(`mulMeasure_singleton_zero`). Local gamma and epsilon factors are characterized by Tate's
local functional equation under its convergence and character conditions
(`IsLocalZetaAdmissible`, `IsLocalGammaFactor`, `IsLocalEpsilonFactorAt`). At a finite place
of a number field it defines conductor exponents through the higher unit groups
`higherUnitsAt` and the local `L`-factors.

The local functional equation is written `Z(f̂, χ⁻¹, 1 - s) = γ * Z(f, χ, s)`, with
`f̂ = tateFourier ψ μ f` in the plus convention: the kernel is `ψ (x * y)`, as in
Definition 4.7 of Poonen's notes. Tate's thesis (§§2.2, 2.4) instead fixes a standard additive
character, takes the Fourier transform with its complex conjugate, and uses the self-dual
additive measure; its functional equation reads `ζ(f, c) = ρ(c) ζ(f̂, ĉ)`. When `ψ` is the
conjugate of the thesis's character, so that `ψ (x * y)` is the thesis's kernel, and `μ` is the
self-dual measure, the equation above for `c = χ |·| ^ s` is the thesis's with `γ = ρ(c)⁻¹`.
For other data the two factors need not agree: replacing `μ` by `t • μ` for a real `t > 0`
multiplies `γ` by `t`, while `ρ(c)` does not change. The local epsilon factor is normalized as
in Tate's Corvallis article and in Theorem 4.18(e) of Poonen's notes:
`ε = γ * L(χ, s) / L(χ⁻¹, 1 - s)` for the same `ψ` and `μ`, so it depends on them too.

## References

* J. T. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Ph.D. thesis,
  Princeton University, 1950; printed in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Academic Press, London, 1967, pp. 305--347.
* J. Tate, *Number theoretic background*, in A. Borel and W. Casselman (eds.),
  *Automorphic Forms, Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part 2,
  Amer. Math. Soc., Providence, RI, 1979, pp. 3--26.
* B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786, Spring 2015,
  <https://math.mit.edu/~poonen/786/notes.pdf>.
-/

@[expose] public section

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped NNReal ENNReal NumberField

namespace LanglandsTunnell.TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K]

/-- **Modulus of a locally compact field.** The factor by which multiplication by `a`
scales Haar measure, and `0` at `a = 0`. -/
public def modulus (a : K) : ℝ≥0 := by
  classical exact if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

@[simp]
public theorem modulus_zero : modulus (0 : K) = 0 := by
  simp [modulus]

public theorem modulus_of_ne_zero {a : K} (h : a ≠ 0) :
    modulus a = distribHaarChar K (Units.mk0 a h) := by
  simp [modulus, h]

@[simp]
public theorem modulus_coe_units (u : Kˣ) : modulus (u : K) = distribHaarChar K u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

public theorem modulus_pos {a : K} (h : a ≠ 0) : 0 < modulus a := by
  rw [modulus_of_ne_zero h]
  exact distribHaarChar_pos

public theorem modulus_ne_zero {a : K} (h : a ≠ 0) : modulus a ≠ 0 :=
  (modulus_pos h).ne'

@[simp]
public theorem modulus_one : modulus (1 : K) = 1 := by
  rw [modulus_of_ne_zero one_ne_zero, Units.mk0_one, map_one]

public theorem modulus_mul (a b : K) : modulus (a * b) = modulus a * modulus b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [modulus_of_ne_zero (mul_ne_zero ha hb), modulus_of_ne_zero ha,
    modulus_of_ne_zero hb, ← map_mul]
  congr 1
  exact Units.ext rfl

end Modulus

section TestFunctions

variable {K : Type*} [TopologicalSpace K]

/-- **Schwartz--Bruhat test function.** A locally constant function of compact support. On a
totally disconnected locally compact group, such as a nonarchimedean local field, these are
the Schwartz--Bruhat functions (Definition 4.6 of Poonen's notes for local fields); on a
general topological space they are only the locally constant part of the classical
Schwartz--Bruhat space (on `ℝ`, only `0`). -/
public def IsSchwartzBruhat (f : K → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

public theorem IsSchwartzBruhat.zero : IsSchwartzBruhat (0 : K → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

public theorem IsSchwartzBruhat.indicator_const {U : Set K} (hU : IsClopen U)
    (hUc : IsCompact U) (c : ℂ) :
    IsSchwartzBruhat (U.indicator fun _ => c) := by
  refine ⟨?_, ?_⟩
  · intro s
    classical
    have hset : (U.indicator fun _ => c) ⁻¹' s =
        (if c ∈ s then U else ∅) ∪ (if (0 : ℂ) ∈ s then Uᶜ else ∅) := by
      ext x
      by_cases hx : x ∈ U <;> by_cases hc : c ∈ s <;>
        by_cases h0 : (0 : ℂ) ∈ s <;>
        simp [Set.indicator, hx, hc, h0]
    rw [hset]
    refine IsOpen.union ?_ ?_
    · split_ifs
      · exact hU.isOpen
      · exact isOpen_empty
    · split_ifs
      · exact hU.compl.isOpen
      · exact isOpen_empty
  · exact HasCompactSupport.intro' hUc hU.isClosed fun x hx =>
      Set.indicator_of_notMem hx _

/-- **Schwartz--Bruhat test space.** The test functions of a topological space, as a complex
submodule of all complex-valued functions. -/
public abbrev testSpace (X : Type*) [TopologicalSpace X] :
    Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X : Type*} [TopologicalSpace X]

public theorem mem_testSpace {f : X → ℂ} :
    f ∈ testSpace X ↔ IsSchwartzBruhat f :=
  Iff.rfl

public theorem mem_testSpace_iff {f : X → ℂ} :
    f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

public theorem isLocallyConstant_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) :
    IsLocallyConstant f :=
  hf.1

public theorem hasCompactSupport_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) :
    HasCompactSupport f :=
  hf.2

public theorem mem_testSpace_of {f : X → ℂ} (h₁ : IsLocallyConstant f)
    (h₂ : HasCompactSupport f) : f ∈ testSpace X :=
  ⟨h₁, h₂⟩

public theorem indicator_mem_testSpace {U : Set X} (hU : IsClopen U)
    (hUc : IsCompact U) (c : ℂ) :
    (U.indicator fun _ => c) ∈ testSpace X :=
  IsSchwartzBruhat.indicator_const hU hUc c

public theorem mul_mem_testSpace {e f : X → ℂ} (he : IsLocallyConstant e)
    (hf : f ∈ testSpace X) : e * f ∈ testSpace X :=
  ⟨he.mul hf.1, hf.2.mul_left⟩

public theorem isClopen_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) :
    IsClopen (Function.support f) := by
  have h : Function.support f = {x | f x = 0}ᶜ := by
    ext x
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_ofPred_eq, ne_eq]
  rw [h]
  exact (hf.1.isClopen_fiber 0).compl

public theorem isCompact_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) :
    IsCompact (Function.support f) :=
  (hasCompactSupport_of_mem hf).isCompact.of_isClosed_subset
    (isClopen_support_of_mem hf).isClosed (subset_tsupport _)

end TestFunctions

section Fourier

variable {K : Type*} [Field K] [MeasurableSpace K]

/-- **Local Fourier transform.** `tateFourier ψ μ f y = ∫ x, f x * ψ (x * y) ∂μ`
(`tateFourier_apply`), in the plus convention: the kernel `ψ (x * y)` and no normalizing
constant, as in Definition 4.7 of Poonen's notes. Tate's thesis uses the complex conjugate of
its additive character instead, which is this kernel for the conjugate character (see the
module docstring). It is `NumberField.AdelicFourier.fourierIntegral`, whose kernel is
`ψ (-(x * y))`, for the inverse character `ψ⁻¹`; equivalently,
`tateFourier ψ μ f y = fourierIntegral ψ μ f (-y)` (`tateFourier_eq_fourierIntegral_neg`).
For any additive character and measure this is a Bochner integral, `0` where the integrand
is not integrable. It is the classical Fourier transform when `K` is a local field, `μ` is an
additive Haar measure and `ψ` is a continuous, nontrivial unitary character (`‖ψ x‖ = 1` for
all `x`); for a continuous nontrivial `ψ` that is not unitary, such as `x ↦ exp x` on `ℝ`, it
is a Laplace-type transform instead. -/
public def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) :
    ℂ :=
  NumberField.AdelicFourier.fourierIntegral ψ⁻¹ μ f y

public theorem tateFourier_apply (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) :
    tateFourier ψ μ f y = ∫ x, f x * ψ (x * y) ∂μ := by
  simp only [tateFourier, NumberField.AdelicFourier.fourierIntegral, AddChar.inv_apply,
    neg_neg]
  congr 1 with x
  exact mul_comm _ _

public theorem tateFourier_zero_fun (ψ : AddChar K ℂ) (μ : Measure K) :
    tateFourier ψ μ (0 : K → ℂ) = 0 := by
  funext y
  exact congrFun (NumberField.AdelicFourier.fourierIntegral_zero ψ⁻¹ μ) y

public theorem tateFourier_eq_fourierIntegral_neg (ψ : AddChar K ℂ) (μ : Measure K)
    (f : K → ℂ) (y : K) :
    tateFourier ψ μ f y = NumberField.AdelicFourier.fourierIntegral ψ μ f (-y) := by
  rw [tateFourier_apply]
  simp only [NumberField.AdelicFourier.fourierIntegral, mul_neg, neg_neg]
  congr 1 with x
  exact mul_comm _ _

end Fourier

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [MeasurableSpace K]

/-- **Multiplicative measure of an additive Haar measure.** The measure `μ(dx) / modulus x`
on `{0}ᶜ`: the restriction of `μ` to `{0}ᶜ`, with density `(modulus x)⁻¹`. When singletons
are measurable, for instance when `K` is Hausdorff or totally disconnected, it gives `{0}`
mass zero (`mulMeasure_singleton_zero`), and on a local field its restriction to `Kˣ` is the
Haar measure `dx / |x|` of `Kˣ` from Tate's thesis (§2.3). Without that hypothesis it can
charge `{0}`: on `ZMod 2` with the indiscrete topology, whose only measurable sets are `∅` and
the whole space, it gives `{0}` positive mass. -/
public def mulMeasure [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] :
    Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹

/-- **The multiplicative measure does not charge zero.** When singletons are measurable,
`mulMeasure μ` gives `{0}` mass zero. This covers every Hausdorff or totally disconnected `K`,
so every field on which `IsLocalZetaAdmissible` is stated. -/
public theorem mulMeasure_singleton_zero [BorelSpace K] [MeasurableSingletonClass K]
    (μ : Measure K) [μ.IsAddHaarMeasure] : mulMeasure μ {0} = 0 := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_singleton 0),
    Measure.restrict_restrict (measurableSet_singleton 0)]
  simp

/-- **Local zeta integral.** `Z(f, χ, s) = ∫ f(x) χ(x) modulus(x) ^ s d×x` for the measure
`d×x = mulMeasure μ` of the additive Haar measure `μ`, where `χ` is extended by zero to `K` as
the multiplicative character `MulChar.ofUnitHom χ`. This is a Bochner integral: for a
continuous `χ` on a local field it is Tate's zeta integral, up to the normalization of the
multiplicative Haar measure, where the integrand is integrable (see `IsLocalZetaAdmissible`),
and it is `0` where the integrand is not integrable, not the value of Tate's meromorphic
continuation. -/
public def localZeta [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * MulChar.ofUnitHom χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)

public theorem localZeta_zero_fun [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (0 : K → ℂ) χ s = 0 := by
  simp [localZeta]

/-- **Admissible data for Tate's local zeta integrals.** The convergence and character
conditions of Tate's local functional equation: `K` is totally disconnected, so that the
locally constant test functions are its Schwartz--Bruhat functions and `mulMeasure μ` gives
`{0}` mass zero (`mulMeasure_singleton_zero`); `ψ` is a continuous nontrivial additive
character; `χ` is a continuous character of `Kˣ`; and for every test function `f` the
integrands of `Z(f, χ, s)` and `Z(f̂, χ⁻¹, 1 - s)`, with `f̂ = tateFourier ψ μ f`, are
integrable for `mulMeasure μ`, so both zeta integrals converge absolutely. The classical theory
takes `ψ` unitary; on a nonarchimedean local field every continuous additive character is. On
a nonarchimedean local field, for a continuous, nontrivial unitary `ψ` and a continuous unitary
`χ`, both integrals converge for every test function when `0 < re s < 1` (Tate's thesis, §2.4;
Theorem 4.18(a) of Poonen's notes, applied to `f` and to `f̂`). On other totally disconnected
fields they can diverge, for instance on `ℚ` with the discrete topology. Outside the range of
absolute convergence Tate's zeta integrals and gamma factor are defined by meromorphic
continuation, which this API does not cover; there the Bochner integrals can be `0` although the
integrals diverge, as for the trivial `χ` at `s = 0` and the indicator of the valuation ring. -/
public structure IsLocalZetaAdmissible [BorelSpace K] [TotallyDisconnectedSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    Prop where
  continuous_addChar : Continuous ψ
  addChar_ne_one : ψ ≠ 1
  continuous_char : Continuous χ
  integrable_zeta : ∀ f ∈ testSpace K,
    Integrable (fun x => f x * MulChar.ofUnitHom χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure μ)
  integrable_zeta_fourier : ∀ f ∈ testSpace K,
    Integrable
      (fun x =>
        tateFourier ψ μ f x * MulChar.ofUnitHom χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure μ)

/-- **Local gamma factor.** `γ` is the local gamma factor of `χ` at `s`, for the additive
character `ψ` and the additive Haar measure `μ`: the data are admissible
(`IsLocalZetaAdmissible`: continuous characters, `ψ` nontrivial, and both zeta integrals
absolutely convergent for every test function), and Tate's local functional equation
`Z(f̂, χ⁻¹, 1 - s) = γ * Z(f, χ, s)`, with `f̂ = tateFourier ψ μ f` in the plus convention,
holds for every test function `f`. By `IsLocalGammaFactor.eq_div` it does not depend on the
test function. It does depend on `ψ` and `μ`: replacing `μ` by `t • μ` for a real `t > 0`
multiplies it by `t`; the module docstring gives data for which it is the reciprocal of the
factor `ρ(c)` of Tate's thesis. Values of `s` outside the range of absolute convergence, where
the gamma factor is defined by meromorphic continuation, are outside its scope. -/
public structure IsLocalGammaFactor [BorelSpace K] [TotallyDisconnectedSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ) (χ : Kˣ →* ℂˣ) (s γ : ℂ) :
    Prop extends IsLocalZetaAdmissible μ ψ χ s where
  functional_equation : ∀ f ∈ testSpace K,
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) = γ * localZeta μ f χ s

/-- **The local gamma factor is a zeta ratio.** A local gamma factor is the ratio of the zeta
integrals of any test function whose zeta integral does not vanish, so it does not depend on
the test function. -/
public theorem IsLocalGammaFactor.eq_div [BorelSpace K] [TotallyDisconnectedSpace K]
    {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s γ : ℂ}
    {f : K → ℂ} (h : IsLocalGammaFactor μ ψ χ s γ) (hf : f ∈ testSpace K)
    (hZ : localZeta μ f χ s ≠ 0) :
    γ = localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s := by
  rw [h.functional_equation f hf, mul_div_cancel_right₀ _ hZ]

/-- **Uniqueness of local gamma factors.** Two local gamma factors agree as soon as one test
function has a nonzero zeta integral. -/
public theorem IsLocalGammaFactor.unique [BorelSpace K] [TotallyDisconnectedSpace K]
    {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s γ γ' : ℂ}
    {f : K → ℂ} (h : IsLocalGammaFactor μ ψ χ s γ) (h' : IsLocalGammaFactor μ ψ χ s γ')
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0) : γ = γ' := by
  rw [h.eq_div hf hZ, h'.eq_div hf hZ]

/-- **Local gamma factor from the symmetric functional equation.** For admissible data, if
`Z(f̂, χ⁻¹, 1 - s) * Z(g, χ, s) = Z(ĝ, χ⁻¹, 1 - s) * Z(f, χ, s)` for all test functions `f`
and `g`, then the ratio of the zeta integrals of a test function `f` with `Z(f, χ, s) ≠ 0` is
the local gamma factor. -/
public theorem isLocalGammaFactor_div_of_mul_comm [BorelSpace K] [TotallyDisconnectedSpace K]
    {μ : Measure K} [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s : ℂ}
    {f : K → ℂ} (hadm : IsLocalZetaAdmissible μ ψ χ s)
    (hsymm : ∀ f ∈ testSpace K, ∀ g ∈ testSpace K,
      localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s =
        localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0) :
    IsLocalGammaFactor μ ψ χ s
      (localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s) :=
  ⟨hadm, fun g hg => by
    rw [div_mul_eq_mul_div, hsymm f hf g hg, mul_div_cancel_right₀ _ hZ]⟩

end Zeta

section Place

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **Conductor exponent.** `χ` has conductor exponent `c` at `v` when `c` is the least level
whose higher unit group lies in the kernel of `χ`. -/
public def HasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (c : ℕ) : Prop :=
  (∀ u ∈ higherUnitsAt K v c, χ u = 1) ∧
    ∀ m < c, ∃ u ∈ higherUnitsAt K v m, χ u ≠ 1

public theorem hasConductorExponentAt_zero_iff
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    HasConductorExponentAt K v χ 0 ↔
      ∀ u : (v.adicCompletion K)ˣ,
        Valued.v (u : v.adicCompletion K) = 1 → χ u = 1 := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnitsAt_zero_iff K v).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnitsAt_zero_iff K v).mp hu),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

public theorem hasConductorExponentAt_unique
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasConductorExponentAt K v χ c)
    (h' : HasConductorExponentAt K v χ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

public theorem hasConductorExponentAt_one_zero :
    HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ _ => rfl

public theorem not_hasConductorExponentAt_one_succ (c : ℕ) :
    ¬ HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

/-- **Extended conductor exponent.** The conductor exponent of `χ` at `v`, in `ℕ∞`. A finite
value `c` means `HasConductorExponentAt K v χ c` (`conductorExponentAt_eq_coe_iff`), that is,
`χ` has the actual finite conductor `𝔭ᵥ ^ c`; `⊤` means that no higher unit group lies in the
kernel of `χ`, so `χ` has no finite conductor (`conductorExponentAt_eq_top_iff`). A continuous
`χ` is trivial on some higher unit group, so its exponent is finite. -/
public def conductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ∞ :=
  ⨅ (c : ℕ) (_ : HasConductorExponentAt K v χ c), (c : ℕ∞)

public theorem conductorExponentAt_eq_of_hasConductorExponentAt
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : HasConductorExponentAt K v χ c) :
    conductorExponentAt K v χ = c := by
  refine le_antisymm (iInf₂_le c h) (le_iInf₂ fun c' h' => ?_)
  rw [hasConductorExponentAt_unique K v h h']

public theorem conductorExponentAt_eq_top_iff
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    conductorExponentAt K v χ = ⊤ ↔ ∀ c, ¬ HasConductorExponentAt K v χ c := by
  simp [conductorExponentAt]

public theorem conductorExponentAt_eq_coe_iff
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} :
    conductorExponentAt K v χ = c ↔ HasConductorExponentAt K v χ c := by
  refine ⟨fun h => ?_, conductorExponentAt_eq_of_hasConductorExponentAt K v⟩
  by_cases hex : ∃ c', HasConductorExponentAt K v χ c'
  · obtain ⟨c', hc'⟩ := hex
    rw [conductorExponentAt_eq_of_hasConductorExponentAt K v hc', Nat.cast_inj] at h
    exact h ▸ hc'
  · rw [(conductorExponentAt_eq_top_iff K v).mpr (not_exists.mp hex)] at h
    exact absurd h.symm (ENat.natCast_ne_top c)

@[simp]
public theorem conductorExponentAt_one :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v
    (hasConductorExponentAt_one_zero K v)

/-- **Local L-factor.** The local `L`-factor of `χ` at `v`: for an unramified character the
Euler factor `(1 - χ ϖ * N(v) ^ (-s))⁻¹` at the uniformizer
`ϖ = NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v`, and `1` for a ramified
character. For a continuous `χ` (a quasi-character in the sense of Tate's thesis, §2.3), this
is the analytic `L`-factor at every `s` that is not a pole. At a pole, where
`χ ϖ * N(v) ^ (-s) = 1` (for the trivial character, at `s = 0`), the formula takes Lean's
`0⁻¹ = 0`, so `localLFactorAt` is `0` there instead of a pole. -/
public def localLFactorAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ := by
  classical exact
    if HasConductorExponentAt K v χ 0 then
      (1 - (χ (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
    else 1

public theorem localLFactorAt_of_hasConductorExponentAt_zero
    {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s
      = (1 - (χ (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt, ite_eq_left hχ]

public theorem localLFactorAt_of_not_hasConductorExponentAt_zero
    {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, ite_eq_right hχ]

public theorem localLFactorAt_one (s : ℂ) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s
      = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v
    (hasConductorExponentAt_one_zero K v), MonoidHom.one_apply,
    Units.val_one, one_mul]

section Epsilon

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [LocallyCompactSpace (v.adicCompletion K)]

/-- **Local epsilon factor.** `ε` is the local epsilon factor of `χ` at `v` and `s`, for the
additive character `ψ` and the additive Haar measure `μ`, when
`ε = γ * L(χ, s) / L(χ⁻¹, 1 - s)` for the local gamma factor `γ` (`IsLocalGammaFactor`, which
includes Tate's convergence and character conditions). The `L`-factors are the values of
`localLFactorAt`, which are `0` at their poles; in the range of absolute convergence that
`IsLocalGammaFactor` requires, neither of them has a pole, so this convention does not
enter. Like `γ`, `ε` depends on `ψ` and `μ`. -/
public def IsLocalEpsilonFactorAt (μ : Measure (v.adicCompletion K))
    [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s ε : ℂ) : Prop :=
  ∃ γ, IsLocalGammaFactor μ ψ χ s γ ∧
    ε = γ * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

/-- **Uniqueness of local epsilon factors.** Two local epsilon factors agree as soon as one
test function has a nonzero zeta integral. -/
public theorem IsLocalEpsilonFactorAt.unique {μ : Measure (v.adicCompletion K)}
    [μ.IsAddHaarMeasure] {ψ : AddChar (v.adicCompletion K) ℂ}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {s ε ε' : ℂ} {f : v.adicCompletion K → ℂ}
    (h : IsLocalEpsilonFactorAt K v μ ψ χ s ε)
    (h' : IsLocalEpsilonFactorAt K v μ ψ χ s ε')
    (hf : f ∈ testSpace (v.adicCompletion K)) (hZ : localZeta μ f χ s ≠ 0) :
    ε = ε' := by
  obtain ⟨γ, hγ, rfl⟩ := h
  obtain ⟨γ', hγ', rfl⟩ := h'
  rw [hγ.unique hγ' hf hZ]

/-- **Local epsilon factors of ramified characters.** For a ramified character both
`L`-factors are `1`, so the local epsilon factors are exactly the local gamma factors. -/
public theorem isLocalEpsilonFactorAt_iff_of_not_hasConductorExponentAt_zero
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s ε : ℂ) :
    IsLocalEpsilonFactorAt K v μ ψ χ s ε ↔ IsLocalGammaFactor μ ψ χ s ε := by
  have hχ' : ¬ HasConductorExponentAt K v χ⁻¹ 0 := fun h => hχ <| by
    rw [hasConductorExponentAt_zero_iff] at h ⊢
    intro u hu
    have h1 := h u hu
    rwa [MonoidHom.inv_apply, inv_eq_one] at h1
  simp only [IsLocalEpsilonFactorAt,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ', mul_one, div_one,
    exists_eq_right']

end Epsilon

end Place

end LanglandsTunnell.TateLocal

end
