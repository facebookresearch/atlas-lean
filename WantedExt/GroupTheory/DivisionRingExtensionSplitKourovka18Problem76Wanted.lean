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

/-- **Palyutin's splitting problem for division rings (Kourovka 18.76).** The statement that for
every division ring $A$, every subgroup $G$ of its unit group $A^\times$ and every group $E$, if
$i$ is an injective homomorphism from the additive group of $A$ to $E$ and $\pi : E \to G$ is a
surjective homomorphism whose kernel is the image of $i$, such that
$e \, i(a) \, e^{-1} = i(\pi(e) a)$ for all $e \in E$ and $a \in A$ (so $G$ acts on the kernel by
left multiplication), then the extension splits: there is a homomorphism $s : G \to E$ with
$\pi(s(g)) = g$ for every $g \in G$. -/
def divisionRingMultiplicationExtensionsSplit : Prop :=
  ∀ (A : Type) [DivisionRing A] (G : Subgroup Aˣ) (E : Type) [Group E]
    (i : Multiplicative A →* E) (π : E →* G), Function.Injective i → Function.Surjective π →
    i.range = π.ker →
    (∀ (e : E) (a : A), e * i (Multiplicative.ofAdd a) * e⁻¹ =
      i (Multiplicative.ofAdd (((π e : Aˣ) : A) * a))) →
    ∃ s : G →* E, ∀ g : G, π (s g) = g

/--
**Extensions of a division ring's additive group by units need not split (Kourovka 18.76).**
There exist a division ring $A$, a subgroup $G$ of its unit group $A^\times$, a group $E$, an
injective homomorphism $i$ from the additive group of $A$ to $E$ and a surjective homomorphism
$\pi : E \to G$ whose kernel is the image of $i$, with $e \, i(a) \, e^{-1} = i(\pi(e) a)$ for all
$e \in E$ and $a \in A$, such that no homomorphism $s : G \to E$ satisfies $\pi(s(g)) = g$ for all
$g \in G$. That is, the splitting statement of Kourovka Problem 18.76 is false.

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
