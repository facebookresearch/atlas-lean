/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.MichaelisMenten
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fed-batch bioreactor: substrate and biomass account

A fed-batch (semi-batch) bioreactor starts with volume `V₀ > 0` and is fed, with no outflow, at
volumetric rate `F(t) ≥ 0` with medium of substrate concentration `S_in ≥ 0` and no biomass. With
the feed and the broth of the same constant density, the volume obeys `V' = F`. Biomass `X` grows
on the substrate `S` at the Monod rate `μ(S) = μ_m S / (K_s + S)` (`mmRate μm Ks` of
Michaelis–Menten kinetics) and consumes `1 / Y` units of substrate per unit of biomass formed;
there is no death or maintenance.
The species balances of the semi-batch reactor, `(V c)' = F c_in + R V`, divided by `V`, give

  `S' = (F / V) (S_in - S) - μ(S) X / Y`,   `X' = μ(S) X - (F / V) X`.

The feed rate is any nonnegative function of time; no continuity of it is assumed. Since
`V' = F` must hold at every time of the interval on which the balances are posed, a feed switched
abruptly is covered by applying the result on each interval between switches, with time measured
from the start of that interval.

## Main definitions

* `IsSolution μ Sin Y F I V S X`: `(V, S, X)` solves these balances, for a growth rate
  `μ : ℝ → ℝ`, on a set `I` of times, with derivatives within `I`.

## Main results

* `IsSolution.substrate_biomass_account`: for Monod growth with `μ_m, K_s, Y > 0`, `S_in ≥ 0`,
  `F ≥ 0`, `V(0) > 0` and `S(0), X(0) ≥ 0`, on an interval `I ∋ 0` and at every time `t ≥ 0` of
  `I`: `V(t) ≥ V(0)`; the stocks `m_S = V S` and `m_X = V X` satisfy
  `(m_S + m_X / Y)' = F S_in`; and `S(t), X(t) ≥ 0`.

The nonnegativity uses only signs, not the Lipschitz continuity of the field. Where `X < 0` and
`S > -K_s`, `X' ≥ μ_m X`, since `μ(S) < μ_m` and `F / V ≥ 0`; where `S < 0`, `S > -K_s` and
`X ≥ 0`, `S' ≥ 0`. A fence argument turns each of these into nonnegativity on an interval, and
continuous induction on `[0, t]` keeps `S` above the pole `-K_s` of the Monod rate.

## References

* J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd
  edition, Nob Hill Publishing: Section 4.4, the semi-batch reactor, Equation 4.44 (p. 131), the
  species balance; Section 4.5, Equation 4.48 (p. 132), the total mass balance, and
  Equation 4.51 (p. 134), its constant-density form `V' = Q_f - Q`; Section 10.5, the
  nonsegregated fermentation model, Equation 10.18 (p. 596), the Monod growth rate and the
  biomass and substrate balances with yield `y`.
-/

@[expose] public section

open Filter Set Real
open scoped Topology

namespace Chemistry.Bioreactors.FedBatch

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)

/-- **Fed-batch bioreactor balances.** The volume `V`, substrate concentration `S` and biomass
concentration `X` solve the fed-batch balances on a set `I` of times, for a specific growth rate
`μ : ℝ → ℝ`, feed substrate concentration `Sin`, yield `Y` and feed rate `F : ℝ → ℝ`, if at every
`t ∈ I`, with derivatives within `I`,

  `V' = F`,   `S' = (F / V) (Sin - S) - μ(S) X / Y`,   `X' = μ(S) X - (F / V) X`

(a quotient by `0` is `0`). Monod growth is `μ = mmRate μm Ks`, `μ(S) = μm S / (Ks + S)`. -/
structure IsSolution (μ : ℝ → ℝ) (Sin Y : ℝ) (F : ℝ → ℝ) (I : Set ℝ) (V S X : ℝ → ℝ) :
    Prop where
  hasDerivWithinAt_volume : ∀ t ∈ I, HasDerivWithinAt V (F t) I t
  hasDerivWithinAt_substrate : ∀ t ∈ I,
    HasDerivWithinAt S (F t / V t * (Sin - S t) - μ (S t) * X t / Y) I t
  hasDerivWithinAt_biomass : ∀ t ∈ I,
    HasDerivWithinAt X (μ (S t) * X t - F t / V t * X t) I t

/-- A fence: if `f` is differentiable on `[a, b]` (within it), `f a ≥ 0`, and `f' t ≥ L f t`
wherever `f t < 0` on `[a, b)`, then `f ≥ 0` on `[a, b]`. No regularity of `f'` is needed. -/
private theorem nonneg_of_hasDerivWithinAt {f f' : ℝ → ℝ} {a b L : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t) (ha : 0 ≤ f a)
    (hneg : ∀ t ∈ Ico a b, f t < 0 → L * f t ≤ f' t) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ f t := by
  by_contra hlt
  rw [not_le] at hlt
  set c := |L| + 1 with hc
  have hE : 0 < exp (c * (t - a)) := exp_pos _
  set ε := -f t / (2 * exp (c * (t - a))) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hcont : ContinuousOn f (Icc a b) := fun u hu ↦ (hf u hu).continuousWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun u ↦ -f u)
    (f' := fun u ↦ -f' u) (B := fun u ↦ ε * exp (c * (u - a)))
    (B' := fun u ↦ c * (ε * exp (c * (u - a)))) hcont.neg
    (fun u hu ↦ ((hf u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu)).neg)
    (by simp only [sub_self, mul_zero, exp_zero, mul_one]; linarith)
    (by fun_prop)
    (fun u _ ↦ by
      have h := ((((hasDerivAt_id' u).sub_const a).const_mul c).exp.const_mul ε).hasDerivWithinAt
        (s := Ici u)
      convert h using 1
      ring)
    (fun u hu heq ↦ by
      have hB : 0 < ε * exp (c * (u - a)) := by positivity
      have hfu : f u = -(ε * exp (c * (u - a))) := by linarith
      have h1 := hneg u hu (by linarith)
      rw [hfu] at h1
      have h2 : L * (ε * exp (c * (u - a))) ≤ |L| * (ε * exp (c * (u - a))) :=
        mul_le_mul_of_nonneg_right (le_abs_self L) hB.le
      rw [hc]
      linarith)
    ht
  have hhalf : ε * exp (c * (t - a)) = -f t / 2 := by
    rw [hε_def]
    field_simp
  simp only [hhalf] at key
  linarith

/-- The Monod rate stays below `μm` above its pole: `μm s / (Ks + s) < μm` for `s > -Ks`. -/
private theorem mmRate_lt_of_neg_lt {μm Ks s : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hs : -Ks < s) :
    mmRate μm Ks s < μm := by
  unfold mmRate
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The Monod rate is nonpositive between its pole and `0`. -/
private theorem mmRate_nonpos {μm Ks s : ℝ} (hμ : 0 ≤ μm) (hs : -Ks < s) (hs0 : s ≤ 0) :
    mmRate μm Ks s ≤ 0 := by
  unfold mmRate
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hμ hs0) (by linarith)

/-- Clause 1: the volume never falls below its initial value. -/
private theorem IsSolution.volume_ge {μ : ℝ → ℝ} {Sin Y : ℝ} {F : ℝ → ℝ} {I : Set ℝ}
    {V S X : ℝ → ℝ} (h : IsSolution μ Sin Y F I V S X) (hI : I.OrdConnected) (h0 : 0 ∈ I)
    (hF : ∀ t ∈ I, 0 ≤ t → 0 ≤ F t) {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) : V 0 ≤ V t := by
  have hsub : Icc 0 t ⊆ I := hI.out h0 ht
  have := nonneg_of_hasDerivWithinAt (f := fun u ↦ V u - V 0) (f' := F) (L := 0)
    (fun u hu ↦ ((h.hasDerivWithinAt_volume u (hsub hu)).sub_const (V 0)).mono hsub)
    (by simp) (fun u hu _ ↦ by
      rw [zero_mul]
      exact hF u (hsub (Ico_subset_Icc_self hu)) hu.1) (right_mem_Icc.2 ht0)
  linarith

/-- Clause 3: for Monod growth, the substrate and the biomass stay nonnegative. -/
private theorem IsSolution.nonneg {μm Ks Sin Y : ℝ} {F : ℝ → ℝ} {I : Set ℝ} {V S X : ℝ → ℝ}
    (h : IsSolution (mmRate μm Ks) Sin Y F I V S X) (hI : I.OrdConnected) (h0 : 0 ∈ I)
    (hμ : 0 < μm) (hK : 0 < Ks) (hSin : 0 ≤ Sin) (hY : 0 < Y)
    (hF : ∀ t ∈ I, 0 ≤ t → 0 ≤ F t) (hV0 : 0 < V 0) (hS0 : 0 ≤ S 0) (hX0 : 0 ≤ X 0)
    {t : ℝ} (ht : t ∈ I) (ht0 : 0 ≤ t) : 0 ≤ S t ∧ 0 ≤ X t := by
  have hsub : Icc 0 t ⊆ I := hI.out h0 ht
  have hVpos : ∀ u ∈ Icc 0 t, 0 < V u := fun u hu ↦
    hV0.trans_le (h.volume_ge hI h0 hF (hsub hu) hu.1)
  have hFV : ∀ u ∈ Icc 0 t, 0 ≤ F u / V u := fun u hu ↦
    div_nonneg (hF u (hsub hu) hu.1) (hVpos u hu).le
  have hSc : ContinuousOn S (Icc 0 t) := fun u hu ↦
    (h.hasDerivWithinAt_substrate u (hsub hu)).continuousWithinAt.mono hsub
  have hXc : ContinuousOn X (Icc 0 t) := fun u hu ↦
    (h.hasDerivWithinAt_biomass u (hsub hu)).continuousWithinAt.mono hsub
  let s : Set ℝ := {u | 0 ≤ S u ∧ 0 ≤ X u}
  have hclosed : IsClosed (s ∩ Icc 0 t) := by
    have h1 := hSc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
    have h2 := hXc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
    convert h1.inter h2 using 1
    ext u
    simp only [s, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici]
    tauto
  refine hclosed.Icc_subset_of_forall_mem_nhdsWithin (show (0 : ℝ) ∈ s from ⟨hS0, hX0⟩) ?_
    (right_mem_Icc.2 ht0)
  rintro x ⟨hxs, hx⟩
  have hxt : x < t := hx.2
  -- Right after `x`, the substrate stays above the pole `-Ks` of the Monod rate.
  have hev : ∀ᶠ u in 𝓝[≥] x, -Ks < S u := by
    have hcw : ContinuousWithinAt S (Icc x t) x :=
      (hSc x (Ico_subset_Icc_self hx)).mono (Icc_subset_Icc_left hx.1)
    rw [← nhdsWithin_Icc_eq_nhdsGE hxt]
    exact hcw.eventually (lt_mem_nhds (by linarith [hxs.1]))
  obtain ⟨u, hxu, hu⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  set c := min u t with hc
  have hxc : x < c := lt_min hxu hxt
  have hsubc : Icc x c ⊆ Icc 0 t := Icc_subset_Icc hx.1 (min_le_right _ _)
  have hSK : ∀ v ∈ Icc x c, -Ks < S v := fun v hv ↦ hu ⟨hv.1, hv.2.trans (min_le_left _ _)⟩
  -- The biomass stays nonnegative on `[x, c]`: where `X < 0`, `X' ≥ μm X`.
  have hX : ∀ v ∈ Icc x c, 0 ≤ X v := by
    intro v hv
    refine nonneg_of_hasDerivWithinAt (L := μm)
      (fun w hw ↦ (h.hasDerivWithinAt_biomass w (hsub (hsubc hw))).mono (hsubc.trans hsub))
      hxs.2 (fun w hw hXw ↦ ?_) hv
    have hw' := Ico_subset_Icc_self hw
    have hlt := mmRate_lt_of_neg_lt hμ hK (hSK w hw')
    have hfv := hFV w (hsubc hw')
    nlinarith
  -- The substrate stays nonnegative on `[x, c]`: where `S < 0`, `S' ≥ 0`.
  have hS : ∀ v ∈ Icc x c, 0 ≤ S v := by
    intro v hv
    refine nonneg_of_hasDerivWithinAt (L := 0)
      (fun w hw ↦ (h.hasDerivWithinAt_substrate w (hsub (hsubc hw))).mono (hsubc.trans hsub))
      hxs.1 (fun w hw hSw ↦ ?_) hv
    have hw' := Ico_subset_Icc_self hw
    have hμS := mmRate_nonpos hμ.le (hSK w hw') hSw.le
    have h1 : mmRate μm Ks (S w) * X w / Y ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hμS (hX w hw')) hY.le
    have h2 : 0 ≤ F w / V w * (Sin - S w) := mul_nonneg (hFV w (hsubc hw')) (by linarith)
    rw [zero_mul]
    linarith
  exact mem_of_superset (Ioo_mem_nhdsGT hxc) fun v hv ↦
    ⟨hS v (Ioo_subset_Icc_self hv), hX v (Ioo_subset_Icc_self hv)⟩

/-- **Fed-batch substrate and biomass account.** Let `μm, Ks > 0` (Monod growth
`μ(S) = μm S / (Ks + S)`), `Sin ≥ 0` and `Y > 0`. Let `I` be an interval containing `0` and let
`(V, S, X)` solve the fed-batch balances `V' = F`, `S' = (F / V) (Sin - S) - μ(S) X / Y`,
`X' = μ(S) X - (F / V) X` on `I`, with derivatives within `I`, for a feed rate `F : ℝ → ℝ` with
`F t ≥ 0` at the times `t ≥ 0` of `I` (no continuity of `F` is assumed), a quotient by `0`
being `0`. If `V 0 > 0`, `S 0 ≥ 0` and `X 0 ≥ 0`, then at every time `t ≥ 0` of `I`:
1. `V t ≥ V 0`;
2. the stocks `m_S = V S` and `m_X = V X` satisfy `(m_S + m_X / Y)' = F Sin`: the function
   `t ↦ V t * S t + V t * X t / Y` has derivative `F t * Sin` at `t` within `I`;
3. `S t ≥ 0` and `X t ≥ 0`. -/
theorem IsSolution.substrate_biomass_account {μm Ks Sin Y : ℝ} {F : ℝ → ℝ} {I : Set ℝ}
    {V S X : ℝ → ℝ} (h : IsSolution (mmRate μm Ks) Sin Y F I V S X) (hI : I.OrdConnected)
    (h0 : 0 ∈ I) (hμ : 0 < μm) (hK : 0 < Ks) (hSin : 0 ≤ Sin) (hY : 0 < Y)
    (hF : ∀ t ∈ I, 0 ≤ t → 0 ≤ F t) (hV0 : 0 < V 0) (hS0 : 0 ≤ S 0) (hX0 : 0 ≤ X 0) :
    (∀ t ∈ I, 0 ≤ t → V 0 ≤ V t) ∧
    (∀ t ∈ I, 0 ≤ t →
      HasDerivWithinAt (fun t ↦ V t * S t + V t * X t / Y) (F t * Sin) I t) ∧
    (∀ t ∈ I, 0 ≤ t → 0 ≤ S t ∧ 0 ≤ X t) := by
  refine ⟨fun t ht ht0 ↦ h.volume_ge hI h0 hF ht ht0, fun t ht ht0 ↦ ?_,
    fun t ht ht0 ↦ h.nonneg hI h0 hμ hK hSin hY hF hV0 hS0 hX0 ht ht0⟩
  have hV : V t ≠ 0 := (hV0.trans_le (h.volume_ge hI h0 hF ht ht0)).ne'
  have hVt := h.hasDerivWithinAt_volume t ht
  convert (hVt.mul (h.hasDerivWithinAt_substrate t ht)).add
    ((hVt.mul (h.hasDerivWithinAt_biomass t ht)).div_const Y) using 1
  field_simp
  ring

end Chemistry.Bioreactors.FedBatch
