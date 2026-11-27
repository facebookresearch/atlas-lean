/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/AcrisImage.lean` and
`ZInQKernel/Contrib/OneProof/FontaineComparison.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingNormal
public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingSeries

/-!
# Fontaine's crystalline period ring `A_cris` inside `B_dR^+`

Let `w` be a generator of the kernel of Fontaine's map `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]`, and let
`A_cris` be the `p`-adic completion of `D = W(𝓞_ℂ_[p]♭)[w^n/n! : n ≥ 1] ⊆ W(𝓞_ℂ_[p]♭)[1/p]`
(`PadicComplexInt.CrystallineCompletion p w`; Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), Exposé II, §2.3.3 p. 78). We construct the natural ring map
`A_cris → B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` (`PadicComplexInt.toBDeRhamPlus`), show that it is
the canonical map on `D` (`PadicComplexInt.toBDeRhamPlus_algebraMap`), that it is injective
(`PadicComplexInt.toBDeRhamPlus_injective`), and that its image is the set of values
`Σ aₙ w^n/n!` with `aₙ ∈ W(𝓞_ℂ_[p]♭)` tending to `0` `p`-adically
(`PadicComplexInt.range_toBDeRhamPlus`). These are the statements of Fontaine, *op. cit.*,
§4.1.2 p. 83.

The map is built level by level: `B_dR^+` is the inverse limit of the quotients
`W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m`, and the value of `x` at level `m` is the class of the partial
sum below `m` of a restricted series representing `x` (`PadicComplexInt.exists_ofRestricted_eq`).
It is well defined because `D` is `p`-adically separated modulo `(ker θ)^m`
(`PadicComplexInt.mem_ker_pow_of_forall`), and injectivity follows from the normalization of the
coefficients (`PadicComplexInt.exists_normalized`, `PadicComplexInt.eq_zero_of_normalized`).
-/

@[expose] public noncomputable section

open Ideal PowerSeries
open WittVector (fontaineTheta)

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/-- The canonical ring map `W(𝓞_ℂ_[p]♭)[1/p] →+* BDeRhamPlus 𝓞_ℂ_[p] p` into the completion along
the kernel of `θ` with `p` inverted. -/
def localizationToBDeRhamPlus : 𝔸ₚ →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  algebraMap 𝔸ₚ (AdicCompletion 𝕀 𝔸ₚ)

variable {p} {w : WittVector p (PreTilt 𝓞_ℂ_[p] p)}

/-! ### Values modulo the powers of `ker θ` -/

/-- `z ∈ W(𝓞_ℂ_[p]♭)[1/p]` represents the value of `x` modulo `(ker θ)^m`: for every `k`, it is a
lift of `x` modulo `p^k`, up to `p^k D + (ker θ)^m`. -/
private def IsVal (m : ℕ) (x : CrystallineCompletion p w) (z : 𝔸ₚ) : Prop :=
  ∀ k, ∃ d : finiteDividedPowers p w,
    AdicCompletion.evalₐ (pIdeal w) k x = Ideal.Quotient.mk _ d ∧
      ∃ e ∈ finiteDividedPowers p w, z - (d : 𝔸ₚ) - (p : 𝔸ₚ) ^ k * e ∈ 𝕀 ^ m

/-- Two representatives in `D` agree modulo `(ker θ)^m` (`D` is `p`-adically separated
modulo `(ker θ)^m`). -/
private theorem IsVal.sub_mem (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {m : ℕ} {x : CrystallineCompletion p w} {z z' : 𝔸ₚ}
    (hz : z ∈ finiteDividedPowers p w) (hz' : z' ∈ finiteDividedPowers p w)
    (h : IsVal m x z) (h' : IsVal m x z') : z - z' ∈ 𝕀 ^ m := by
  refine mem_ker_pow_of_forall hgen (Subring.sub_mem _ hz hz') m fun k => ?_
  have hk := h k
  have hk' := h' k
  obtain ⟨d, hd, e, he, hz1⟩ := hk
  obtain ⟨d', hd', e', he', hz2⟩ := hk'
  have hdd : d - d' ∈ pIdeal w ^ k := Ideal.Quotient.eq.mp (hd.symm.trans hd')
  have hdd' := (mem_pIdeal_pow_iff w k (d - d')).mp hdd
  obtain ⟨e'', he'', hde⟩ := hdd'
  refine ⟨e'' + e - e', Subring.sub_mem _ (Subring.add_mem _ he'' he) he', ?_⟩
  have hc : ((d - d' : finiteDividedPowers p w) : 𝔸ₚ) = (d : 𝔸ₚ) - d' := rfl
  rw [hc] at hde
  have key : z - z' - (p : 𝔸ₚ) ^ k * (e'' + e - e') =
      (z - d - (p : 𝔸ₚ) ^ k * e) - (z' - d' - (p : 𝔸ₚ) ^ k * e') +
        ((d : 𝔸ₚ) - d' - (p : 𝔸ₚ) ^ k * e'') := by
    ring
  rw [key, hde, sub_self, add_zero]
  exact Ideal.sub_mem _ hz1 hz2

private theorem isVal_ofRestricted (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0) {f : 𝔸⟦X⟧}
    (hf : f ∈ restrictedPowerSeries p) (m : ℕ) :
    IsVal m (ofRestricted w hf) (dividedPowerSum w f m) := by
  intro k
  refine ⟨dividedPowerSumD w f (decayBound hf k), evalₐ_ofRestricted w hf k _ le_rfl, ?_⟩
  have hsum := exists_sum_eq_pow_mul_sum w (k := k) (f := f)
    (Finset.Ico (decayBound hf k) (max m (decayBound hf k)))
    fun n hn => decayBound_spec hf k n (Finset.mem_Ico.mp hn).1
  obtain ⟨g, hg⟩ := hsum
  refine ⟨∑ n ∈ Finset.Ico (decayBound hf k) (max m (decayBound hf k)),
      algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n g) * dividedPower w n,
    sum_mul_dividedPower_mem w _ _, ?_⟩
  rw [← hg, ← dividedPowerSum_sub_dividedPowerSum w f (le_max_right m (decayBound hf k))]
  have hc : (dividedPowerSumD w f (decayBound hf k) : 𝔸ₚ) =
      dividedPowerSum w f (decayBound hf k) := rfl
  have key : dividedPowerSum w f m - (dividedPowerSumD w f (decayBound hf k) : 𝔸ₚ) -
      (dividedPowerSum w f (max m (decayBound hf k)) - dividedPowerSum w f (decayBound hf k)) =
      -(dividedPowerSum w f (max m (decayBound hf k)) - dividedPowerSum w f m) := by
    rw [hc]
    ring
  rw [key]
  exact neg_mem (dividedPowerSum_sub_mem_ker_pow w hw f (le_max_left m _))

private theorem isVal_add {m : ℕ} {x y : CrystallineCompletion p w} {z z' : 𝔸ₚ}
    (h : IsVal m x z) (h' : IsVal m y z') : IsVal m (x + y) (z + z') := by
  intro k
  have hk := h k
  have hk' := h' k
  obtain ⟨d, hd, e, he, hz1⟩ := hk
  obtain ⟨d', hd', e', he', hz2⟩ := hk'
  refine ⟨d + d', (map_add (AdicCompletion.evalₐ (pIdeal w) k) x y).trans
    ((congrArg₂ (· + ·) hd hd').trans ((Ideal.Quotient.mk _).map_add d d').symm),
    e + e', Subring.add_mem _ he he', ?_⟩
  have hc : ((d + d' : finiteDividedPowers p w) : 𝔸ₚ) = (d : 𝔸ₚ) + d' := rfl
  have key : z + z' - ((d + d' : finiteDividedPowers p w) : 𝔸ₚ) -
      (p : 𝔸ₚ) ^ k * (e + e') =
      (z - d - (p : 𝔸ₚ) ^ k * e) + (z' - d' - (p : 𝔸ₚ) ^ k * e') := by
    rw [hc]
    ring
  rw [key]
  exact Ideal.add_mem _ hz1 hz2

private theorem isVal_mul {m : ℕ} {x y : CrystallineCompletion p w} {z z' : 𝔸ₚ}
    (h : IsVal m x z) (h' : IsVal m y z') (hz' : z' ∈ finiteDividedPowers p w) :
    IsVal m (x * y) (z * z') := by
  intro k
  have hk := h k
  have hk' := h' k
  obtain ⟨d, hd, e, he, hz1⟩ := hk
  obtain ⟨d', hd', e', he', hz2⟩ := hk'
  refine ⟨d * d', (map_mul (AdicCompletion.evalₐ (pIdeal w) k) x y).trans
    ((congrArg₂ (· * ·) hd hd').trans ((Ideal.Quotient.mk _).map_mul d d').symm),
    e * z' + d * e',
    Subring.add_mem _ (Subring.mul_mem _ he hz') (Subring.mul_mem _ d.2 he'), ?_⟩
  have hc : ((d * d' : finiteDividedPowers p w) : 𝔸ₚ) = (d : 𝔸ₚ) * d' := rfl
  have key : z * z' - ((d * d' : finiteDividedPowers p w) : 𝔸ₚ) -
      (p : 𝔸ₚ) ^ k * (e * z' + d * e') =
      (z - d - (p : 𝔸ₚ) ^ k * e) * z' + (d : 𝔸ₚ) * (z' - d' - (p : 𝔸ₚ) ^ k * e') := by
    rw [hc]
    ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hz1) (Ideal.mul_mem_left _ _ hz2)

private theorem isVal_one (m : ℕ) : IsVal m (1 : CrystallineCompletion p w) 1 := by
  intro k
  refine ⟨1, (map_one (AdicCompletion.evalₐ (pIdeal w) k)).trans (map_one _).symm, 0,
    Subring.zero_mem _, ?_⟩
  have key : (1 : 𝔸ₚ) - ((1 : finiteDividedPowers p w) : 𝔸ₚ) -
      (p : 𝔸ₚ) ^ k * 0 = 0 := by
    rw [OneMemClass.coe_one]
    ring
  rw [key]
  exact Ideal.zero_mem _

private theorem isVal_zero (m : ℕ) : IsVal m (0 : CrystallineCompletion p w) 0 := by
  intro k
  refine ⟨0, (map_zero (AdicCompletion.evalₐ (pIdeal w) k)).trans (map_zero _).symm, 0,
    Subring.zero_mem _, ?_⟩
  have key : (0 : 𝔸ₚ) - ((0 : finiteDividedPowers p w) : 𝔸ₚ) -
      (p : 𝔸ₚ) ^ k * 0 = 0 := by
    rw [ZeroMemClass.coe_zero]
    ring
  rw [key]
  exact Ideal.zero_mem _

/-! ### The ring map `A_cris → B_dR^+` -/

/-- If the kernel of `θ` is generated by `w`, then `θ(w) = 0`. -/
theorem fontaineTheta_eq_zero_of_ker_eq_span
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    fontaineTheta 𝓞_ℂ_[p] p w = 0 := by
  change w ∈ RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p)
  rw [hgen]
  exact mem_span_singleton_self w

/-- If the kernel of `θ` is generated by `w`, then the image of `w` in `W(𝓞_ℂ_[p]♭)[1/p]` lies in
the kernel of `θ` with `p` inverted. -/
theorem algebraMap_mem_ker_of_ker_eq_span
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) : algebraMap 𝔸 𝔸ₚ w ∈ 𝕀 :=
  algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_eq_zero_of_ker_eq_span hgen)

variable (w)

/-- A restricted series representing `x` (chosen using `exists_ofRestricted_eq`). -/
def rep (x : CrystallineCompletion p w) : 𝔸⟦X⟧ :=
  Classical.choose (exists_ofRestricted_eq w x)

/-- The chosen representative of `x` is a restricted series. -/
theorem rep_mem (x : CrystallineCompletion p w) : rep w x ∈ restrictedPowerSeries p :=
  (Classical.choose_spec (exists_ofRestricted_eq w x)).fst

/-- The chosen representative of `x` defines `x`. -/
theorem ofRestricted_rep (x : CrystallineCompletion p w) : ofRestricted w (rep_mem w x) = x :=
  (Classical.choose_spec (exists_ofRestricted_eq w x)).snd

/-- The value of `x` in `W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m`: the class of the partial sum below `m` of
the chosen representative of `x`. -/
def levelValue (m : ℕ) (x : CrystallineCompletion p w) : 𝔸ₚ ⧸ 𝕀 ^ m :=
  Ideal.Quotient.mk _ (dividedPowerSum w (rep w x) m)

variable {w}

private theorem isVal_rep (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0) (m : ℕ)
    (x : CrystallineCompletion p w) : IsVal m x (dividedPowerSum w (rep w x) m) := by
  have h := isVal_ofRestricted hw (rep_mem w x) m
  rwa [ofRestricted_rep] at h

private theorem levelValue_eq_of_isVal
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {m : ℕ} {x : CrystallineCompletion p w} {z : 𝔸ₚ} (hz : z ∈ finiteDividedPowers p w)
    (h : IsVal m x z) : levelValue w m x = Ideal.Quotient.mk _ z :=
  Ideal.Quotient.eq.mpr ((isVal_rep (fontaineTheta_eq_zero_of_ker_eq_span hgen) m x).sub_mem hgen
    (dividedPowerSum_mem w _ m) hz h)

/-- For a generator `w` of the kernel of `θ`, the value at level `m` as a ring map
`CrystallineCompletion p w →+* W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m`. -/
def levelRingHom (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (m : ℕ) :
    CrystallineCompletion p w →+* 𝔸ₚ ⧸ 𝕀 ^ m where
  toFun := levelValue w m
  map_one' := by
    exact (levelValue_eq_of_isVal hgen (Subring.one_mem _) (isVal_one m)).trans (map_one _)
  map_mul' x y := by
    exact (levelValue_eq_of_isVal hgen
      (Subring.mul_mem _ (dividedPowerSum_mem w _ m) (dividedPowerSum_mem w _ m))
      (isVal_mul (isVal_rep (fontaineTheta_eq_zero_of_ker_eq_span hgen) m x)
        (isVal_rep (fontaineTheta_eq_zero_of_ker_eq_span hgen) m y)
        (dividedPowerSum_mem w _ m))).trans (map_mul (Ideal.Quotient.mk _) _ _)
  map_zero' := by
    exact (levelValue_eq_of_isVal hgen (Subring.zero_mem _) (isVal_zero m)).trans (map_zero _)
  map_add' x y := by
    exact (levelValue_eq_of_isVal hgen
      (Subring.add_mem _ (dividedPowerSum_mem w _ m) (dividedPowerSum_mem w _ m))
      (isVal_add (isVal_rep (fontaineTheta_eq_zero_of_ker_eq_span hgen) m x)
        (isVal_rep (fontaineTheta_eq_zero_of_ker_eq_span hgen) m y))).trans
      (map_add (Ideal.Quotient.mk _) _ _)

/-- `levelRingHom hgen m` sends `x` to its value `levelValue w m x`. -/
theorem levelRingHom_apply (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) (x : CrystallineCompletion p w) : levelRingHom hgen m x = levelValue w m x := rfl

/-- For a generator `w` of the kernel of `θ`, the values at the levels `m ≤ n` are compatible
with the projection `W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^n → W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m`. -/
theorem factorPow_comp_levelRingHom
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow 𝕀 hle).comp (levelRingHom hgen n) = levelRingHom hgen m := by
  ext x
  change Ideal.Quotient.factorPow 𝕀 hle
      (Ideal.Quotient.mk (𝕀 ^ n) (dividedPowerSum w (rep w x) n)) =
    Ideal.Quotient.mk (𝕀 ^ m) (dividedPowerSum w (rep w x) m)
  exact (Ideal.Quotient.factor_mk _ _).trans (Ideal.Quotient.eq.mpr
    (dividedPowerSum_sub_mem_ker_pow w (fontaineTheta_eq_zero_of_ker_eq_span hgen) _ hle))

/-- For a generator `w` of the kernel of `θ`, the natural ring map from the `p`-adic completion
of `W(𝓞_ℂ_[p]♭)[w^n/n!]` (Fontaine's `A_cris`) to `BDeRhamPlus 𝓞_ℂ_[p] p`: the limit of the
values at the levels `W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m`. -/
def toBDeRhamPlus (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    CrystallineCompletion p w →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  AdicCompletion.liftRingHom 𝕀 (levelRingHom hgen) (factorPow_comp_levelRingHom hgen)

/-- The image of `toBDeRhamPlus hgen x` in `W(𝓞_ℂ_[p]♭)[1/p] / (ker θ)^m` is the value of `x` at
level `m`. -/
theorem evalₐ_toBDeRhamPlus (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (m : ℕ) (x : CrystallineCompletion p w) :
    AdicCompletion.evalₐ 𝕀 m (toBDeRhamPlus hgen x) = levelValue w m x :=
  AdicCompletion.evalₐ_liftRingHom 𝕀 (levelRingHom hgen) (factorPow_comp_levelRingHom hgen) m x

/-- On the element defined by a restricted series `f = Σ aₙ Xⁿ`, the map `toBDeRhamPlus hgen` is
the value `Σ aₙ w^n/n!` in `BDeRhamPlus 𝓞_ℂ_[p] p` of the divided-power series of `f`. -/
theorem toBDeRhamPlus_ofRestricted (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) :
    toBDeRhamPlus hgen (ofRestricted w hf) =
      evalBDeRhamPlus p (algebraMap_mem_ker_of_ker_eq_span hgen) (dividedPowerSeries p f) := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  refine (evalₐ_toBDeRhamPlus hgen m _).trans ?_
  refine Eq.trans ?_
    (evalₐ_evalBDeRhamPlus_dividedPowerSeries w (fontaineTheta_eq_zero_of_ker_eq_span hgen)
      f m).symm
  exact levelValue_eq_of_isVal hgen (dividedPowerSum_mem w f m)
    (isVal_ofRestricted (fontaineTheta_eq_zero_of_ker_eq_span hgen) hf m)

/-- On `W(𝓞_ℂ_[p]♭)[w^n/n!]` itself, the map `toBDeRhamPlus hgen` is the canonical map
`W(𝓞_ℂ_[p]♭)[w^n/n!] ⊆ W(𝓞_ℂ_[p]♭)[1/p] → BDeRhamPlus 𝓞_ℂ_[p] p`. -/
theorem toBDeRhamPlus_algebraMap (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    (x : finiteDividedPowers p w) :
    toBDeRhamPlus hgen (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
      localizationToBDeRhamPlus p (x : 𝔸ₚ) := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  refine (evalₐ_toBDeRhamPlus hgen m _).trans ?_
  have hv : IsVal m (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x)
      (x : 𝔸ₚ) := by
    intro k
    refine ⟨x, AdicCompletion.evalₐ_of _ k x, 0, Subring.zero_mem _, ?_⟩
    rw [show (x : 𝔸ₚ) - (x : 𝔸ₚ) - (p : 𝔸ₚ) ^ k * 0 = 0 by ring]
    exact Ideal.zero_mem _
  exact (levelValue_eq_of_isVal hgen x.2 hv).trans (AdicCompletion.evalₐ_of 𝕀 m (x : 𝔸ₚ)).symm

/-! ### Image and injectivity -/

/-- For a generator `w` of the kernel of `θ`, the image of the map `A_cris → B_dR^+` is the set
of values `Σ aₙ w^n/n!` in `BDeRhamPlus 𝓞_ℂ_[p] p` of the divided-power series of the
restricted series `Σ aₙ Xⁿ` over `W(𝓞_ℂ_[p]♭)`. -/
theorem range_toBDeRhamPlus (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    Set.range (toBDeRhamPlus hgen) =
      {y | ∃ f ∈ restrictedPowerSeries p,
        y = evalBDeRhamPlus p (algebraMap_mem_ker_of_ker_eq_span hgen)
          (dividedPowerSeries p f)} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [← ofRestricted_rep w x, toBDeRhamPlus_ofRestricted hgen]
    exact ⟨rep w x, rep_mem w x, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨ofRestricted w hf, toBDeRhamPlus_ofRestricted hgen hf⟩

/-- An element of `A_cris` that maps to `0` in `B_dR^+` is `0`. -/
theorem eq_zero_of_toBDeRhamPlus_eq_zero
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {x : CrystallineCompletion p w} (hx : toBDeRhamPlus hgen x = 0) : x = 0 := by
  have hnorm := exists_normalized hgen (rep_mem w x)
  obtain ⟨g, hg, hgn, hfg⟩ := hnorm
  have hphi : ofRestricted w (rep_mem w x) = ofRestricted w hg :=
    ofRestricted_eq_of_forall w _ _ hfg
  have h0 : ∀ m, dividedPowerSum w g m ∈ 𝕀 ^ m := by
    intro m
    have h1 : AdicCompletion.evalₐ 𝕀 m (toBDeRhamPlus hgen x) = 0 := by
      rw [hx]
      exact map_zero _
    rw [← ofRestricted_rep w x, hphi, toBDeRhamPlus_ofRestricted hgen,
      evalₐ_evalBDeRhamPlus_dividedPowerSeries w (fontaineTheta_eq_zero_of_ker_eq_span hgen),
      Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hg0 : g = 0 := eq_zero_of_normalized hgen hgn h0
  subst hg0
  rw [← ofRestricted_rep w x, hphi]
  exact ofRestricted_zero w

/-- For a generator `w` of the kernel of `θ`, the map `A_cris → B_dR^+` is injective. -/
theorem toBDeRhamPlus_injective
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    Function.Injective (toBDeRhamPlus hgen) := by
  intro x y hxy
  have h : toBDeRhamPlus hgen (x - y) = 0 := by
    rw [(toBDeRhamPlus hgen).map_sub x y, hxy, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_toBDeRhamPlus_eq_zero hgen h)

/-- Fontaine, *Le corps des périodes p-adiques*, Exposé II, §§2.3.3 and 4.1.2: for a generator
`w` of the kernel of `θ`, there is an injective ring map from the `p`-adic completion of
`W(𝓞_ℂ_[p]♭)[w^n/n!]` to `BDeRhamPlus 𝓞_ℂ_[p] p` that agrees with the canonical map on
`W(𝓞_ℂ_[p]♭)[w^n/n!]` and whose image is the set of values `Σ aₙ w^n/n!` with
`aₙ ∈ W(𝓞_ℂ_[p]♭)` tending to `0` `p`-adically. -/
theorem exists_injective_crystallineCompletion_bDeRhamPlus
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) :
    ∃ j : CrystallineCompletion p w →+* BDeRhamPlus 𝓞_ℂ_[p] p, Function.Injective j ∧
      (∀ x : finiteDividedPowers p w,
        j (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
          localizationToBDeRhamPlus p (x : 𝔸ₚ)) ∧
      Set.range j =
        {y | ∃ f ∈ restrictedPowerSeries p,
          y = evalBDeRhamPlus p (algebraMap_mem_ker_of_ker_eq_span hgen)
            (dividedPowerSeries p f)} :=
  ⟨toBDeRhamPlus hgen, toBDeRhamPlus_injective hgen, toBDeRhamPlus_algebraMap hgen,
    range_toBDeRhamPlus hgen⟩

end PadicComplexInt
