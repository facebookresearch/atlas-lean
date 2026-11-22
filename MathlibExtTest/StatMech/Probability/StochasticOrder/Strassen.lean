/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StochasticOrder.Strassen

/-!
# Tests for `MathlibExt.Probability.StochasticOrder.Strassen`

* `StatMech.MonotoneCoupling`: the Dirac mass at `(⊥, ⊤)` is a monotone coupling of `δ_⊥` and
  `δ_⊤` on any finite configuration space (all three fields proved).
* `StatMech.MonotoneCoupling.stochasticallyDominated` (the easy half of Strassen's theorem): applied
  to it on `Fin 2`, giving `δ_⊥ ≼ δ_⊤`; `total_mass_eq` is applied too.
* `StatMech.orderSet`: membership decided on `Fin 2`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.StochasticOrder.Strassen

open MeasureTheory
open _root_.StatMech

/-- `(⊥, ⊤)` is an ordered pair, `(⊤, ⊥)` is not (on `Fin 2`). -/
example : ((⊥, ⊤) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) ∈ orderSet (Fin 2) ∧
    ((⊤, ⊥) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) ∉ orderSet (Fin 2) := by
  exact ⟨show (⊥ : ConfigSpace (Fin 2)) ≤ ⊤ from bot_le, fun h => absurd (h 0) (by decide)⟩

/-- `δ_(⊥, ⊤)` is a monotone coupling of `δ_⊥` and `δ_⊤`. -/
theorem monotoneCoupling_dirac (E : Type*) [Finite E] :
    MonotoneCoupling (Measure.dirac (⊥ : ConfigSpace E)) (Measure.dirac ⊤)
      (Measure.dirac (⊥, ⊤)) where
  fst_eq := by rw [Measure.fst, Measure.map_dirac' measurable_fst]
  snd_eq := by rw [Measure.snd, Measure.map_dirac' measurable_snd]
  supported := by
    rw [Measure.dirac_apply' _ measurableSet_orderSet.compl]
    exact Set.indicator_of_notMem
      (show ((⊥, ⊤) : ConfigSpace E × ConfigSpace E) ∉ (orderSet E)ᶜ from
        fun h => h (show (⊥ : ConfigSpace E) ≤ ⊤ from bot_le)) _

/-- The two marginals of the coupling have equal mass. -/
example (E : Type*) [Finite E] :
    Measure.dirac (⊥ : ConfigSpace E) Set.univ = Measure.dirac (⊤ : ConfigSpace E) Set.univ :=
  (monotoneCoupling_dirac E).total_mass_eq

/-- The easy half of Strassen's theorem applied to the coupling. -/
example : StochasticallyDominated (Measure.dirac (⊥ : ConfigSpace (Fin 2))) (Measure.dirac ⊤) :=
  (monotoneCoupling_dirac (Fin 2)).stochasticallyDominated

end MathlibExtTest.StatMech.Probability.StochasticOrder.Strassen
