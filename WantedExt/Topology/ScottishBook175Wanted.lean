/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

namespace MathlibExt.Topology.ScottishBook175Wanted

/-- The Hilbert cube `Q`, as the countable product of closed unit intervals. -/
abbrev ScottishBookHilbertCube : Type := ℕ → ↥(Set.Icc (0 : ℝ) 1)

/-- The curve shaped like the letter `T`: a vertical stem with a horizontal
bar on top, with branch point `(0, 1)`. -/
abbrev ScottishBookLetterT : Set (ℝ × ℝ) :=
  {p | (p.1 = 0 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∨ (p.2 = 1 ∧ p.1 ∈ Set.Icc (-1 : ℝ) 1)}

/--
Borsuk's Problem 175 from the Scottish Book, both parts affirmative:
(a) the Cartesian product of the Hilbert cube `Q` with the letter-`T`
curve is homeomorphic to `Q`; (b) the product of an infinite sequence
of copies of the letter-`T` curve is homeomorphic to `Q`. Source:
K. Borsuk, Problem 175 of the Scottish Book; positively solved by
R. D. Anderson, as cited in Domoradzki-Stawiska-Zarichnyi, "90+ years of
the Scottish Book" (arXiv:2603.27867), and in the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted borsuk175_hilbert_cube_times_letterT :
    Nonempty (ScottishBookHilbertCube × ↥ScottishBookLetterT ≃ₜ
      ScottishBookHilbertCube) ∧
    Nonempty ((ℕ → ↥ScottishBookLetterT) ≃ₜ ScottishBookHilbertCube)

end MathlibExt.Topology.ScottishBook175Wanted
