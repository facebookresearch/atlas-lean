/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A germ representation of Baumslag's group (Kourovka Notebook Problem 17.99)

Kourovka Notebook, Problem 17.99 (A. Yu. Olshanskii): consider the group `B = ⟨a, b | (bab⁻¹) a
(bab⁻¹)⁻¹ = a²⟩` introduced by Baumslag in 1969. The same relation is satisfied by `f(x) = 2x` and
`g(x) = 2^x` under composition in the group of germs of monotonically increasing to `∞` continuous
functions on `(0, ∞)` (functions identified when they coincide for all sufficiently large
arguments). Is the representation `a ↦ f`, `b ↦ g` of `B` faithful?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BaumslagGroupGermsFaithfulKourovka17Problem99Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.99 (A. Yu. Olshanskii). UnsolvedMath
record UM-00701401 (`KOU-17.99`), dataset ulamai/UnsolvedMath v1.8.0.

The representation is written on words: an element `w` of the free group on `a, b` acts by the
composite of `x ↦ 2x`, `x ↦ x/2`, `x ↦ 2^x`, `x ↦ log₂ x` along its reduced word, the first letter
applied last, so that products are composites; with this order the defining relator acts as the
identity for `x > 0`. Faithful means: if the function of `w` agrees with the identity for all large
`x` (`=ᶠ[Filter.atTop]`), then `w` is trivial in `B`. Values of `log₂` at non-positive arguments do
not matter, as every composite tends to `∞`.
-/

/-- Baumslag's group `B = ⟨a, b | (b a b⁻¹) a (b a b⁻¹)⁻¹ = a²⟩`, with `a = x₀`, `b = x₁`. -/
abbrev BaumslagGroup : Type :=
  PresentedGroup ({(FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) * FreeGroup.of 0 *
      (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)⁻¹ * (FreeGroup.of 0 ^ 2)⁻¹} :
      Set (FreeGroup (Fin 2)))

/-- The function attached to a letter: `a ↦ f(x) = 2x`, `a⁻¹ ↦ x/2`, `b ↦ g(x) = 2^x` and
`b⁻¹ ↦ log₂ x` (the inverse of `g` for large `x`, which is all that matters for germs at `+∞`). -/
noncomputable def letterFunction : Fin 2 × Bool → ℝ → ℝ
  | (0, true) => fun x => 2 * x
  | (0, false) => fun x => x / 2
  | (1, true) => fun x => (2 : ℝ) ^ x
  | (1, false) => fun x => Real.logb 2 x

/-- The function attached to an element of the free group on `a, b`: the composite of the letter
functions along its reduced word, the first letter applied last, so that products of germs are
composites (`(φ ψ)(x) = φ (ψ x)`); with this order `f` and `g` satisfy the defining relation of
`B` as germs at `+∞`. -/
noncomputable def wordFunction (w : FreeGroup (Fin 2)) : ℝ → ℝ :=
  (FreeGroup.toWord w).foldr (fun l h => letterFunction l ∘ h) id

/-- Kourovka 17.99 (A. Yu. Olshanskii): the representation `a ↦ f`, `b ↦ g` of Baumslag's group
`B` in the group of germs at `+∞` of increasing continuous functions on `(0, ∞)` is faithful: an
element of the free group whose function is eventually the identity is trivial in `B`. -/
def baumslagGroupGermRepresentationFaithful : Prop :=
  ∀ w : FreeGroup (Fin 2), wordFunction w =ᶠ[Filter.atTop] id →
    (PresentedGroup.mk _ w : BaumslagGroup) = 1

/--
Resolved false: Nyberg-Brodda exhibits a non-trivial element of Baumslag's group `B = BG(1, 2)` in
the kernel of the representation `a ↦ 2x`, `b ↦ 2^x` by germs at `+∞`; the Kourovka Notebook (21st
issue) answers 17.99 "No, it is not". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
17.99 (A. Yu. Olshanskii); resolution: C.-F. Nyberg-Brodda, The Baumslag-Gersten group and a problem
of Olshanskii, preprint, arXiv:2606.27408 (2026), abstract (the representation of BG(1, 2) by germs
is not faithful: an explicit non-trivial element of its kernel); the Kourovka Notebook (21st issue)
marks 17.99 solved (No, it is not), https://arxiv.org/abs/2606.27408.
-/
public theorem_wanted baumslagGroupGermRepresentationFaithful_refuted :
    ¬ baumslagGroupGermRepresentationFaithful

end MathlibExt.GroupTheory.BaumslagGroupGermsFaithfulKourovka17Problem99Wanted
