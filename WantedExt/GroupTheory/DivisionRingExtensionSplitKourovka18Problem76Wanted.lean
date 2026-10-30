/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Extensions of the additive group of a division ring (Kourovka Notebook Problem 18.76)

Kourovka Notebook, Problem 18.76 (E. A. Palyutin), marked solved in the 21st issue: let `A` be a
division ring, `G` a subgroup of the multiplicative group of `A`, and `E` an extension of the
additive group of `A` by `G` such that `G` acts by multiplication in `A`. Is it true that `E`
splits? This is true if `G` is finite.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

namespace MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.76 (E. A. Palyutin). UnsolvedMath record
UM-00701505 (`KOU-18.76`), dataset ulamai/UnsolvedMath v1.8.0.

The extension is an injective `i : Multiplicative A →* E` and a surjective `π : E →* G` with `range
i = ker π` and `e · i(a) · e⁻¹ = i(π(e) a)` (left multiplication, the action in the resolving
construction); it splits when `π` has a homomorphic section. The resolution is by AI-generated
solutions confirmed by B. A. F. Wehrfritz.
-/

/-- Kourovka 18.76 (E. A. Palyutin): let `A` be a division ring and `G` a subgroup of `Aˣ`. Every
extension `E` of the additive group of `A` by `G` in which `G` acts by multiplication splits. The
extension is an injective `i : A → E` (on the additive group of `A`, written multiplicatively) and a
surjective `π : E → G` with `range i = ker π` and `e · i(a) · e⁻¹ = i(π(e) a)`; it splits when `π`
has a homomorphic section. -/
def divisionRingMultiplicationExtensionsSplit : Prop :=
  ∀ (A : Type) [DivisionRing A] (G : Subgroup Aˣ) (E : Type) [Group E]
    (i : Multiplicative A →* E) (π : E →* G), Function.Injective i → Function.Surjective π →
    i.range = π.ker →
    (∀ (e : E) (a : A), e * i (Multiplicative.ofAdd a) * e⁻¹ =
      i (Multiplicative.ofAdd (((π e : Aˣ) : A) * a))) →
    ∃ s : G →* E, ∀ g : G, π (s g) = g

/--
Resolved false: the Kourovka Notebook (21st issue) answers 18.76 "No, not always", by AI-generated
solutions confirmed by B. A. F. Wehrfritz (Jayadevan; Kinyon-Urban, 2026). In Kinyon-Urban, `G = F ×
L` is a product of two free groups of rank `2` inside a division ring `D` (Mal'cev-Neumann), and an
extension of `(D, +)` by `G` with conjugation acting by left multiplication has no splitting.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.76 (E. A. Palyutin); resolution: M.
Kinyon and J. Urban, Results on problems from the Kourovka Notebook, preprint, version 4, 19
September 2026; Achyuth Jayadevan, preprint of 14 September 2026,
https://zenodo.org/records/22751423, Kinyon-Urban Section 3.28: G = F × L with F, L free of rank 2,
D the division closure of kG in a Mal'cev-Neumann division ring (k = Q or a prime field), and a
nonsplit extension of (D, +) by G whose conjugation action on the kernel is left multiplication; AI
solutions confirmed by B. A. F. Wehrfritz, accepted in the Kourovka Notebook (21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted divisionRingMultiplicationExtensionsSplit_refuted :
    ¬ divisionRingMultiplicationExtensionsSplit

end MathlibExt.GroupTheory.DivisionRingExtensionSplitKourovka18Problem76Wanted
