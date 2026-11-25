/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

namespace MathlibExt.MeasureTheory.ScottishBook170Wanted

/--
**Szpilrajn's Problem 170: plane sets with measurable homeomorphic copies.** Let $S$ be a subset
of the plane $\mathbb{R}^2$ such that every subset $T$ of $\mathbb{R}^2$ homeomorphic to $S$ (as
a subspace) is Lebesgue measurable, that is, Carathéodory measurable with respect to Lebesgue
outer measure on $\mathbb{R}^2$. Then $S$ is absolutely measurable: for every measure $\mu$ on
the Borel $\sigma$-algebra of $\mathbb{R}^2$, the set $S$ is Carathéodory measurable with respect
to the outer measure induced by $\mu$.

The hypothesis concerns every subset of the plane homeomorphic to $S$, not only the images of $S$
under homeomorphisms of the whole plane.

Source: E. Szpilrajn, Problem 170 of the Scottish
Book; the affirmative answer follows from an unpublished result of
J. von Neumann, as recorded in Ad 170 of the typescript. See the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed.
(Birkhäuser, 2015). Lebesgue measurability is stated as Carathéodory
measurability with respect to `volume`; the case of linear sets, and
the analogue for generalized homeomorphisms in the sense of Kuratowski,
were already known.
-/
theorem_wanted szpilrajn170_homeomorphic_images_measurable_imp_absolute :
    ∀ S : Set (ℝ × ℝ),
      (∀ T : Set (ℝ × ℝ), Nonempty (↥S ≃ₜ ↥T) →
        @MeasurableSet (ℝ × ℝ) (MeasureTheory.volume.toOuterMeasure.caratheodory) T) →
      ∀ μ : MeasureTheory.Measure (ℝ × ℝ),
        @MeasurableSet (ℝ × ℝ) (μ.toOuterMeasure.caratheodory) S

end MathlibExt.MeasureTheory.ScottishBook170Wanted
