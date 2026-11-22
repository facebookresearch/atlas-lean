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

/-- Kourovka 16.57 (V. D. Mazurov): every group, finite or not, whose set of element orders is
`{1, 2, 3, 4, 7} = ω(L₂(7))` is isomorphic to `L₂(7) = PSL(2, 7)`. -/
def spectrumRecognizesPSL27 : Prop :=
  ∀ (G : Type) [Group G], Set.range (orderOf : G → ℕ) = {1, 2, 3, 4, 7} →
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))

/--
Resolved true: the Kourovka Archive answers 16.57 "Yes, it is", citing Lytkina and Kuznetsov (2007):
every group, finite or infinite, with spectrum `{1, 2, 3, 4, 7}` is isomorphic to `L₂(7)`. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.57 (V. D. Mazurov);
resolution: D. V. Lytkina and A. A. Kuznetsov, Sib. Èlektron. Mat. Izv. 4 (2007), 136-140, Kourovka
Archive, Problem 16.57 (Yes, it is).
-/
public theorem_wanted spectrumRecognizesPSL27_holds : spectrumRecognizesPSL27

end MathlibExt.GroupTheory.SpectrumRecognitionPSL27Kourovka16Problem57Wanted
