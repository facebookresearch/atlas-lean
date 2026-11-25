/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliShift
public import MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
public import Mathlib.Probability.UniformOn

/-!
# Non-isomorphism of the uniform three- and two-symbol Bernoulli shifts

The one-sided shifts are distinguished by the size of a fiber. Translating the first symbol
preserves the uniform product law, so almost every ternary sequence lies in a fiber on which
the conjugacy and left-inverse identities hold at all three points.
-/

public section

namespace MathlibExt.Dynamics.KolmogorovSinaiWanted

open MeasureTheory
open MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy MathlibExt.Dynamics.Ergodic.BernoulliShift

private def rotateHead (i : Fin 3) (x : ℕ → Fin 3) (n : ℕ) : Fin 3 :=
  x n + if n = 0 then i else 0

private theorem measurePreserving_rotateHead (i : Fin 3) :
    let μ := Measure.infinitePi fun _ : ℕ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3))
    MeasurePreserving (rotateHead i) μ μ := by
  let p := ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3))
  have hmap (b : Fin 3) : p.map (· + b) = p := by
    apply Measure.ext_of_singleton
    intro a
    have hpre : (fun z : Fin 3 => z + b) ⁻¹' {a} = {a - b} := by
      ext z
      exact eq_sub_iff_add_eq.symm
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _), hpre]
    simp [p, ProbabilityTheory.uniformOn_univ]
  let f (n : ℕ) (z : Fin 3) := z + if n = 0 then i else 0
  have hf (n : ℕ) : Measurable (f n) := measurable_of_finite _
  refine ⟨Measurable.of_eval fun n => (hf n).comp (measurable_pi_apply n), ?_⟩
  exact (Measure.infinitePi_map_pi (fun _ : ℕ => p) hf).trans
    (congrArg Measure.infinitePi (funext fun n => hmap (if n = 0 then i else 0)))

/-- **Kolmogorov's non-isomorphism of Bernoulli schemes.** The `(1/3, 1/3, 1/3)` and the
`(1/2, 1/2)` Bernoulli schemes are not measure-theoretically isomorphic, even modulo null sets
(`IsIsomorphicMod0`, the notion of O. Sarig, *Lecture Notes on Ergodic Theory*, Definition 1.3),
because their entropies are `log 3 ≠ log 2` (Sarig, Proposition 4.6). Fixed and periodic points
form null sets, so counting them proves nothing here: entropy is needed. -/
theorem not_isomorphic_bernoulli_uniform_three_two :
    ¬ IsIsomorphicMod0
      (Measure.infinitePi fun _ : ℕ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3)))
      (shift : (ℕ → Fin 3) → ℕ → Fin 3)
      (Measure.infinitePi fun _ : ℕ => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2)))
      (shift : (ℕ → Fin 2) → ℕ → Fin 2) := by
  rintro ⟨π, ρ, _, _, hleft, _, hshift, _⟩
  have hgood := ae_all_iff.2 fun i => (measurePreserving_rotateHead i).quasiMeasurePreserving.ae
    (hleft.and hshift)
  obtain ⟨x, hx⟩ := hgood.exists
  have htail (i : Fin 3) : shift (π (rotateHead i x)) = π (shift x) := by
    have h : shift (rotateHead i x) = shift x := by
      funext n
      simp [shift_apply, rotateHead]
    exact (hx i).2.symm.trans (congrArg π h)
  apply Fintype.not_injective_of_card_lt (fun i => π (rotateHead i x) 0) (by decide)
  intro i j hij
  have heq : π (rotateHead i x) = π (rotateHead j x) := by
    funext n
    cases n with
    | zero => exact hij
    | succ n => simpa only [shift_apply] using congrFun ((htail i).trans (htail j).symm) n
  have hrot : rotateHead i x = rotateHead j x :=
    (hx i).1.symm.trans ((congrArg ρ heq).trans (hx j).1)
  simpa [rotateHead] using congrFun hrot 0

end MathlibExt.Dynamics.KolmogorovSinaiWanted
