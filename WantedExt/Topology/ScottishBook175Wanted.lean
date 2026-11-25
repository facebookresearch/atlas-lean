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

/-- **The Hilbert cube.** The Hilbert cube $Q = [0,1]^{\mathbb{N}}$ is the product of countably
many copies of the closed unit interval $[0,1]$, with the product topology. -/
abbrev ScottishBookHilbertCube : Type := ℕ → ↥(Set.Icc (0 : ℝ) 1)

/-- **The letter T.** The letter-T curve is the subset
$$T = \{(0, y) : 0 \le y \le 1\} \cup \{(x, 1) : -1 \le x \le 1\}$$
of $\mathbb{R}^2$: a vertical stem with a horizontal bar on top, meeting at the branch point
$(0, 1)$. -/
abbrev ScottishBookLetterT : Set (ℝ × ℝ) :=
  {p | (p.1 = 0 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∨ (p.2 = 1 ∧ p.1 ∈ Set.Icc (-1 : ℝ) 1)}

/--
**The Hilbert cube absorbs the letter T (Borsuk's Problem 175).** Let $Q = [0,1]^{\mathbb{N}}$ be
the Hilbert cube and let $T \subset \mathbb{R}^2$ be the letter-T curve. Both parts of Borsuk's
Problem 175 from the Scottish Book have affirmative answers: (a) the product $Q \times T$ is
homeomorphic to $Q$, and (b) the product $T^{\mathbb{N}}$ of countably many copies of $T$ is
homeomorphic to $Q$.

Source:
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
