/-
Copyright (c) 2025–2026 the contributors.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.BurgersUniqueness
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Burgers evolution laws

For bounded continuous real initial data and positive constant viscosity, the
Cole–Hopf construction is independent of its spatial normalization anchor and
satisfies the restart and semigroup laws at nonnegative times. The zero-time
identity is the existing `burgersSolution_zero` theorem.

More generally, any classical field in the whole-half-line uniqueness class
can be restarted from any nonnegative time. Shifting time preserves continuity,
positive-time `C²` regularity and the PDE; boundedness on the shifted strip follows
from boundedness on a longer original strip. No bound uniform over all times or
initial spatial derivative is required. No assertion about negative durations or
finite-lifespan competitors is made.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace ColeHopf

/-- The spatial normalization anchor does not affect the Burgers evolution. -/
theorem burgersSolution_anchor_independent {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν) (a b t x : ℝ) (ht : 0 ≤ t) :
    burgersSolution ν u₀ a t x = burgersSolution ν u₀ b t x := by
  have hs := eq_burgersSolution hν
    (burgersSolution_continuous_of_bounded hu hb hν a).continuousOn
    (burgersSolution_contDiffOn_of_bounded hu hb hν a)
    (fun _ _ => by
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, fun s _ y => abs_burgersSolution_le hu hν hM a s y⟩)
    (fun s hs y => burgersSolution_burgers_of_bounded hu hb hν a s y hs) b t ht x
  have h0 : burgersSolution ν u₀ a 0 = u₀ :=
    funext (burgersSolution_zero hu hν.ne' a)
  simpa only [h0] using hs

/-- Restart any admissible classical Burgers field from a nonnegative time.
The spatial normalization anchor of the restarted explicit solution is arbitrary. -/
theorem burgers_restart {u : ℝ → ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun r => u r x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    u (s + t) x = burgersSolution ν (u s) a t x := by
  have hsc : ContinuousOn (Function.uncurry (fun r y => u (s + r) y)) (Ici 0 ×ˢ univ) :=
    hc.comp ((continuousOn_const.add continuousOn_fst).prodMk continuousOn_snd)
      (fun _ hp => ⟨add_nonneg hs hp.1, hp.2⟩)
  have hsu : ContDiffOn ℝ 2 (Function.uncurry (fun r y => u (s + r) y)) (Ioi 0 ×ˢ univ) :=
    hu.comp ((contDiffOn_const.add contDiffOn_fst).prodMk contDiffOn_snd)
      (fun _ hp => ⟨add_pos_of_nonneg_of_pos hs hp.1, hp.2⟩)
  have hsb : ∀ T, 0 ≤ T → ∃ M, ∀ r ∈ Icc 0 T, ∀ y, |u (s + r) y| ≤ M := by
    intro T hT
    obtain ⟨M, hM⟩ := hb (s + T) (add_nonneg hs hT)
    exact ⟨M, fun r hr y => hM (s + r)
      ⟨add_nonneg hs hr.1, add_le_add le_rfl hr.2⟩ y⟩
  have hsp : ∀ r, 0 < r → ∀ y,
      deriv (fun q => u (s + q) y) r + u (s + r) y * deriv (u (s + r)) y =
        ν * iteratedDeriv 2 (u (s + r)) y := by
    intro r hr y
    rw [deriv_comp_const_add (fun q => u q y) s r]
    exact hpde (s + r) (add_pos_of_nonneg_of_pos hs hr) y
  simpa only [add_zero] using eq_burgersSolution hν hsc hsu hsb hsp a t ht x

/-- Evolving for `s` and restarting for `t` equals evolving for `s + t`, even
when the two constructions use different spatial normalization anchors. -/
theorem burgersSolution_restart {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν)
    (a b s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a s) b t x =
      burgersSolution ν u₀ a (s + t) x := by
  apply (burgers_restart hν
    (burgersSolution_continuous_of_bounded hu hb hν a).continuousOn
    (burgersSolution_contDiffOn_of_bounded hu hb hν a)
    (fun _ _ => by
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, fun r _ y => abs_burgersSolution_le hu hν hM a r y⟩)
    (fun r hr y => burgersSolution_burgers_of_bounded hu hb hν a r y hr) b s t x hs ht).symm

/-- The semigroup law as equality of spatial functions, for nonnegative durations. -/
theorem burgersSolution_semigroup {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν : ℝ} (hν : 0 < ν)
    (a s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    burgersSolution ν (burgersSolution ν u₀ a s) a t = burgersSolution ν u₀ a (s + t) :=
  funext (fun x => burgersSolution_restart hu hb hν a a s t x hs ht)

end ColeHopf
