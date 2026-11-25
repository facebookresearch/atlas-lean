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
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import MathlibExt.NumberTheory.NumberField.HeckeCharacter

@[expose] public section

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped NNReal ENNReal NumberField

namespace TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K]

/-- The modulus character of a locally compact field: the factor by which
multiplication by `a` scales Haar measure. -/
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

/-- A Schwartz--Bruhat test function: a locally constant function of compact
support. On a general topological space this is the locally constant,
compactly supported part of the classical Schwartz--Bruhat space. -/
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

/-- The Schwartz--Bruhat test space of a topological space, as a complex
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

/-- The local Fourier transform of `f` with respect to an additive character
`ψ` and a measure `μ`, evaluated at `y`. -/
public def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) :
    ℂ :=
  ∫ x, f x * ψ (x * y) ∂μ

public theorem tateFourier_zero_fun (ψ : AddChar K ℂ) (μ : Measure K) :
    tateFourier ψ μ (0 : K → ℂ) = 0 := by
  funext y
  simp [tateFourier]

end Fourier

section Characters

variable {K : Type*} [Field K]

/-- Extension by zero of a multiplicative character of `Kˣ` to all of `K`. -/
public def charExt (χ : Kˣ →* ℂˣ) (x : K) : ℂ := by
  classical exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

@[simp]
public theorem charExt_zero (χ : Kˣ →* ℂˣ) : charExt χ (0 : K) = 0 := by
  simp [charExt]

public theorem charExt_of_ne_zero (χ : Kˣ →* ℂˣ) {x : K} (h : x ≠ 0) :
    charExt χ x = χ (Units.mk0 x h) := by
  simp [charExt, h]

@[simp]
public theorem charExt_coe_units (χ : Kˣ →* ℂˣ) (u : Kˣ) :
    charExt χ (u : K) = χ u := by
  rw [charExt_of_ne_zero χ u.ne_zero, Units.mk0_val]

public theorem charExt_one_of_ne_zero {x : K} (h : x ≠ 0) :
    charExt (1 : Kˣ →* ℂˣ) x = 1 := by
  rw [charExt_of_ne_zero _ h, MonoidHom.one_apply, Units.val_one]

end Characters

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [MeasurableSpace K]

/-- The multiplicative Haar measure `μ(dx) / modulus x` attached to an
additive Haar measure `μ`, as a measure on `K` carried by `{0}ᶜ`. -/
public def mulMeasure [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] :
    Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹

/-- The local zeta integral `Z(f, χ, s)` for the additive Haar measure `μ`. -/
public def localZeta [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)

public theorem localZeta_zero_fun [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (0 : K → ℂ) χ s = 0 := by
  simp [localZeta]

/-- `γ` is a local gamma factor of `χ` at `s`, for the additive character `ψ`
and the additive Haar measure `μ`: Tate's local functional equation
`Z(f̂, χ⁻¹, 1 - s) = γ * Z(f, χ, s)`, with `f̂ = tateFourier ψ μ f`, holds for
every Schwartz--Bruhat test function `f`. The zeta integrals are Lebesgue
integrals, so this is the gamma factor where they converge (for a unitary `χ`,
when `0 < re s < 1`). By `IsLocalGammaFactor.eq_div` it does not depend on
the test function. -/
public def IsLocalGammaFactor [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    (ψ : AddChar K ℂ) (χ : Kˣ →* ℂˣ) (s γ : ℂ) : Prop :=
  ∀ f ∈ testSpace K,
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) = γ * localZeta μ f χ s

/-- A local gamma factor is the ratio of the zeta integrals of any test
function whose zeta integral does not vanish, so it does not depend on the
test function. -/
public theorem IsLocalGammaFactor.eq_div [BorelSpace K] {μ : Measure K}
    [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s γ : ℂ} {f : K → ℂ}
    (h : IsLocalGammaFactor μ ψ χ s γ) (hf : f ∈ testSpace K)
    (hZ : localZeta μ f χ s ≠ 0) :
    γ = localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s := by
  rw [h f hf, mul_div_cancel_right₀ _ hZ]

/-- Two local gamma factors agree as soon as one test function has a nonzero
zeta integral. -/
public theorem IsLocalGammaFactor.unique [BorelSpace K] {μ : Measure K}
    [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s γ γ' : ℂ} {f : K → ℂ}
    (h : IsLocalGammaFactor μ ψ χ s γ) (h' : IsLocalGammaFactor μ ψ χ s γ')
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0) : γ = γ' := by
  rw [h.eq_div hf hZ, h'.eq_div hf hZ]

/-- From the symmetric form of the local functional equation,
`Z(f̂, χ⁻¹, 1 - s) * Z(g, χ, s) = Z(ĝ, χ⁻¹, 1 - s) * Z(f, χ, s)` for all test
functions `f` and `g`, the ratio of the zeta integrals of a test function `f`
with `Z(f, χ, s) ≠ 0` is a local gamma factor. -/
public theorem isLocalGammaFactor_div_of_mul_comm [BorelSpace K] {μ : Measure K}
    [μ.IsAddHaarMeasure] {ψ : AddChar K ℂ} {χ : Kˣ →* ℂˣ} {s : ℂ} {f : K → ℂ}
    (hsymm : ∀ f ∈ testSpace K, ∀ g ∈ testSpace K,
      localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s =
        localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0) :
    IsLocalGammaFactor μ ψ χ s
      (localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s) := by
  intro g hg
  rw [div_mul_eq_mul_div, hsymm f hf g hg, mul_div_cancel_right₀ _ hZ]

end Zeta

section Place

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The `n`-th higher unit group of the completion at `v`: units congruent
to `1` modulo the `n`-th power of the maximal ideal (all valuation-one units
when `n = 0`). -/
public def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤
      WithZero.exp (-(n : ℤ)))}

public theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤
        WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

public theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

public theorem one_mem_higherUnitsAt (n : ℕ) :
    (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

public theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))

/-- `χ` has conductor exponent `c` at `v` when `c` is the least level whose
higher unit group lies in the kernel of `χ`. -/
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

/-- The conductor exponent of `χ` at `v`: the `c` with
`HasConductorExponentAt K v χ c`, or `⊤` when there is none, that is, when no
higher unit group lies in the kernel of `χ`. -/
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

/-- The local `L`-factor at `v`: the usual Euler factor for an unramified
character, and `1` for a ramified character. -/
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

/-- `ε` is a local epsilon factor of `χ` at `v` and `s`, for the additive
character `ψ` and the additive Haar measure `μ`, when
`ε = γ * L(χ, s) / L(χ⁻¹, 1 - s)` for a local gamma factor `γ`. -/
public def IsLocalEpsilonFactorAt (μ : Measure (v.adicCompletion K))
    [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s ε : ℂ) : Prop :=
  ∃ γ, IsLocalGammaFactor μ ψ χ s γ ∧
    ε = γ * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

/-- Two local epsilon factors agree as soon as one test function has a
nonzero zeta integral. -/
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

/-- For a ramified character both `L`-factors are `1`, so the local epsilon
factors are exactly the local gamma factors. -/
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

end TateLocal

end
