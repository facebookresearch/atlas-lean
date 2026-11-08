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

/-- `f`, a continuous function on the open interval `(0, 1)`, has a
derivative at every point of `(0, 1)`: differentiability is tested on the
extension of `f` to `ℝ` that is `0` outside `(0, 1)`, which agrees with `f`
near every point of `(0, 1)`, so differentiability at such a point depends
only on `f`. -/
def HasDerivativeAtEveryPoint (f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ)) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
    DifferentiableAt ℝ (fun y => if h : y ∈ Set.Ioo (0 : ℝ) 1 then f ⟨y, h⟩ else 0) x

/--
Banach, Problem 52 of the Scottish Book. Original claim, to be shown: the
class of functions that are continuous on the interval `(0, 1)` and have a
derivative at every point does not form a Borel set in the space `C` of all
continuous functions on `(0, 1)`. The typescript itself records that this
class is not an `F_σ` set and that it is a `CA` (coanalytic) set, and that
the problem was solved by Mazurkiewicz. Formalized here as the non-Borel
claim, the problem's headline statement.
Source: S. Banach, Problem 52 of the Scottish Book; solved by Mazurkiewicz,
as recorded in typescript Ad 52; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted everywhere_differentiable_class_not_borel :
    ¬ MeasurableSet { f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ) | HasDerivativeAtEveryPoint f }

end MathlibExt.Topology.ScottishBook52Wanted
