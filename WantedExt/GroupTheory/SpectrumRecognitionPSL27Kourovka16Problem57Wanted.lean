/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with the spectrum of `L₂(7)` (Kourovka Notebook Problem 16.57)

Kourovka Notebook, Archive of Solved Problems, Problem 16.57 (V. D. Mazurov): suppose that `ω(G) =
ω(L₂(7)) = {1, 2, 3, 4, 7}`. Is `G ≅ L₂(7)`? This is true for finite `G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.SpectrumRecognitionPSL27Kourovka16Problem57Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.57 (V. D.
Mazurov). UnsolvedMath record UM-00701249 (`KOU-16.57`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is an arbitrary group in `Type`, possibly infinite; its spectrum is the set of element orders,
so an element of infinite order (`orderOf = 0`) is excluded by the hypothesis. `L₂(7) = PSL(2, 7)`
is Mathlib's `Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)`.
-/

/-- **Kourovka Problem 16.57: recognition of PSL(2, 7) by spectrum.** The statement that every
group $G$, finite or infinite, whose set of element orders $\{\operatorname{ord}(g) : g \in G\}$
equals $\{1, 2, 3, 4, 7\}$ is isomorphic to $L_2(7) = \mathrm{PSL}(2, 7)$, the projective special
linear group of $2 \times 2$ matrices over the field $\mathbb{Z}/7\mathbb{Z}$. -/
def spectrumRecognizesPSL27 : Prop :=
  ∀ (G : Type) [Group G], Set.range (orderOf : G → ℕ) = {1, 2, 3, 4, 7} →
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))

/--
**Lytkina–Kuznetsov theorem: PSL(2, 7) is recognizable by spectrum.** Every group $G$, finite or
infinite, whose set of element orders $\{\operatorname{ord}(g) : g \in G\}$ equals
$\{1, 2, 3, 4, 7\}$ is isomorphic to $L_2(7) = \mathrm{PSL}(2, 7)$, the projective special linear
group of $2 \times 2$ matrices over the field $\mathbb{Z}/7\mathbb{Z}$.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.57 (V. D. Mazurov);
resolution: D. V. Lytkina and A. A. Kuznetsov, Sib. Èlektron. Mat. Izv. 4 (2007), 136-140, Kourovka
Archive, Problem 16.57 (Yes, it is).
-/
public theorem_wanted spectrumRecognizesPSL27_holds : spectrumRecognizesPSL27

end MathlibExt.GroupTheory.SpectrumRecognitionPSL27Kourovka16Problem57Wanted
