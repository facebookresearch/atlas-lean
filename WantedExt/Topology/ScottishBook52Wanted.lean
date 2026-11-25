/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace MathlibExt.Topology.ScottishBook52Wanted

/-- **Functions differentiable at every point of $(0, 1)$.** A continuous function
$f \colon (0, 1) \to \mathbb{R}$ has a derivative at every point if for every $x \in (0, 1)$ the
function $\tilde f \colon \mathbb{R} \to \mathbb{R}$ equal to $f$ on $(0, 1)$ and to $0$ outside
$(0, 1)$ is differentiable at $x$. Since $\tilde f$ agrees with $f$ near every point of $(0, 1)$,
this depends only on $f$: it says that $f$ is differentiable at every point of $(0, 1)$. -/
def HasDerivativeAtEveryPoint (f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ)) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
    DifferentiableAt ℝ (fun y => if h : y ∈ Set.Ioo (0 : ℝ) 1 then f ⟨y, h⟩ else 0) x

/--
**Everywhere differentiable functions do not form a Borel set.** In the space $C((0, 1))$ of
continuous real functions on the open interval $(0, 1)$, with the compact-open topology (uniform
convergence on compact subsets), the set of functions that have a derivative at every point of
$(0, 1)$ is not a Borel set.

This is Banach's Problem 52 of the Scottish Book. The typescript also records that this class is
not an $F_\sigma$ set, that it is coanalytic, and that the problem was solved by Mazurkiewicz.

Source: S. Banach, Problem 52 of the Scottish Book; solved by Mazurkiewicz,
as recorded in typescript Ad 52; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted everywhere_differentiable_class_not_borel :
    ¬ MeasurableSet { f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ) | HasDerivativeAtEveryPoint f }

end MathlibExt.Topology.ScottishBook52Wanted
