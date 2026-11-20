/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.MonotoneAutomatonInterpolation
import Code.FrontierA.MassTransport

open MeasureTheory

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


abbrev PairSiteConfig (d : ℕ) := ConfigSpace (Site d ⊕ Site d)


def pairSiteConfig (eta zeta : ConfigSpace (Site d)) : PairSiteConfig d
  | Sum.inl x => eta x
  | Sum.inr x => zeta x


def pairSiteLeft (omega : PairSiteConfig d) : ConfigSpace (Site d) :=
  fun x => omega (Sum.inl x)


def pairSiteRight (omega : PairSiteConfig d) : ConfigSpace (Site d) :=
  fun x => omega (Sum.inr x)

@[simp] theorem pairSiteLeft_pair (eta zeta : ConfigSpace (Site d)) :
    pairSiteLeft (pairSiteConfig eta zeta) = eta := rfl

@[simp] theorem pairSiteRight_pair (eta zeta : ConfigSpace (Site d)) :
    pairSiteRight (pairSiteConfig eta zeta) = zeta := rfl


theorem measurable_pairSiteConfig : Measurable
    (Function.uncurry pairSiteConfig :
      (ConfigSpace (Site d) × ConfigSpace (Site d)) → PairSiteConfig d) := by
  rw [measurable_pi_iff]
  intro e
  cases e with
  | inl x => exact (measurable_pi_apply x).comp measurable_fst
  | inr x => exact (measurable_pi_apply x).comp measurable_snd

theorem measurable_pairSiteLeft :
    Measurable (pairSiteLeft : PairSiteConfig d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  exact fun x => measurable_pi_apply (Sum.inl x)

theorem measurable_pairSiteRight :
    Measurable (pairSiteRight : PairSiteConfig d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  exact fun x => measurable_pi_apply (Sum.inr x)


theorem pairSiteConfig_shift (g : Multiplicative (Site d))
    (eta zeta : ConfigSpace (Site d)) :
    pairSiteConfig (shift g eta) (shift g zeta) =
      shift g (pairSiteConfig eta zeta) := by
  funext e
  cases e <;> rfl


noncomputable def interpolatedHighPair (T : MonotoneAutomaton d)
    (q : FieldTriple d) : PairSiteConfig d :=
  pairSiteConfig (interpolatedSite T q) (T q.2.2)

@[simp] theorem pairSiteLeft_interpolatedHighPair
    (T : MonotoneAutomaton d) (q : FieldTriple d) :
    pairSiteLeft (interpolatedHighPair T q) = interpolatedSite T q := rfl

@[simp] theorem pairSiteRight_interpolatedHighPair
    (T : MonotoneAutomaton d) (q : FieldTriple d) :
    pairSiteRight (interpolatedHighPair T q) = T q.2.2 := rfl


theorem measurable_interpolatedHighPair (T : MonotoneAutomaton d) :
    Measurable (interpolatedHighPair T : FieldTriple d → PairSiteConfig d) := by
  unfold interpolatedHighPair
  exact measurable_pairSiteConfig.comp
    ((measurable_interpolatedSite T).prodMk
      (T.measurable_toFun.comp measurable_snd.snd))


theorem interpolatedHighPair_shift (T : MonotoneAutomaton d)
    (g : Multiplicative (Site d)) (q : FieldTriple d) :
    interpolatedHighPair T (tripleFieldShift g q) =
      shift g (interpolatedHighPair T q) := by
  unfold interpolatedHighPair
  rw [interpolatedSite_shift, tripleFieldShift_snd_snd,
    T.equivariant, pairSiteConfig_shift]


noncomputable def interpolatedHighPairLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) : Measure (PairSiteConfig d) :=
  Measure.map (interpolatedHighPair T) mu



theorem interpolatedHighPairLaw_isTranslationInvariant
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    (hinv : IsTripleFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (interpolatedHighPairLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold interpolatedHighPairLaw
  rw [Measure.map_map (measurable_shift g) (measurable_interpolatedHighPair T)]
  have hcomp :
      (shift g : PairSiteConfig d → PairSiteConfig d) ∘ interpolatedHighPair T =
        interpolatedHighPair T ∘ (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
    funext q
    exact (interpolatedHighPair_shift T g q).symm
  rw [hcomp,
    ← Measure.map_map (measurable_interpolatedHighPair T)
      (measurable_tripleFieldShift g),
    (hinv g).map_eq]



theorem interpolatedHighPair_nested (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    pairSiteLeft (interpolatedHighPair T q) ≤
      pairSiteRight (interpolatedHighPair T q) :=
  (monotoneAutomaton_interpolation_sandwich T q hq).2.1.trans
    (monotoneAutomaton_interpolation_sandwich T q hq).2.2

end StatMech.FrontierA
