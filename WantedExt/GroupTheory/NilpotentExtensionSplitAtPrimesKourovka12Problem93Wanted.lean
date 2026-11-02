/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nilpotent extensions that split at every prime need not split (Kourovka 12.93)

Kourovka Notebook, Problem 12.93 (P. Hilton): Let `N ↣ G ↠ Q` be an extension of nilpotent groups,
with `Q` finitely generated, which splits at every prime. Does the extension split? This is known to
be true if `N` is finite or commutative. Archive of Solved Problems: No, not always (K. Lorensen,
Math. Proc. Cambridge Philos. Soc. 123, no. 2 (1998), 213-215).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.93 (P.
Hilton). UnsolvedMath record UM-00700910 (`KOU-12.93`), dataset ulamai/UnsolvedMath v1.8.0.

Reading: 'splits at every prime' is read as in Hilton's localization theory and in Lorensen's paper:
for every prime `p` the `p`-localized extension `N_p ↣ G_p ↠ Q_p` splits. The `p`-localization of a
nilpotent group is given by its universal property (Hilton, Mislin and Roitberg): a homomorphism to
a nilpotent `p`-local group (`x ↦ xⁿ` bijective for every `n` coprime to `p`) through which every
homomorphism to a nilpotent `p`-local group factors uniquely. The localized extension splits iff the
localized quotient map `π_p : G_p →* Q_p` has a homomorphic section; since localizations are unique
up to unique isomorphism, this does not depend on the chosen localizations. An extension splits iff
its quotient map has a homomorphic section. The answer is stated as the negation of the universal
claim, with groups in `Type`.
-/

/-- **$p$-local groups.** Let $p$ be a natural number. A group $H$ is $p$-local when, for every
natural number $n$ coprime to $p$, the map $x \mapsto x^n$ is a bijection of $H$.

This is the notion of a $P$-local group of Hilton, Mislin and Roitberg, for $P$ the set whose only
element is $p$. -/
def IsPLocal (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun x : H => x ^ n

/-- **$p$-localization of a group.** Let $p$ be a natural number. A homomorphism of groups
$e \colon G \to L$ is a $p$-localization when $L$ is nilpotent and $p$-local, and every
homomorphism $f$ from $G$ to a nilpotent $p$-local group $H$ factors uniquely through $e$: there is
exactly one homomorphism $g \colon L \to H$ with $g \circ e = f$. -/
def IsPLocalization (p : ℕ) {G L : Type} [Group G] [Group L] (e : G →* L) : Prop :=
  Group.IsNilpotent L ∧ IsPLocal p L ∧
    ∀ (H : Type) [Group H], Group.IsNilpotent H → IsPLocal p H →
      ∀ f : G →* H, ∃! g : L →* H, g.comp e = f

/-- **Splitting at a prime.** Let $p$ be a natural number and $\pi \colon G \to Q$ a homomorphism
of groups (in the intended use, the quotient map of an extension). Then $\pi$ splits at $p$ when
there exist $p$-localizations $e_G \colon G \to G_p$ and $e_Q \colon Q \to Q_p$ and homomorphisms
$\pi_p \colon G_p \to Q_p$ and $s \colon Q_p \to G_p$ with $\pi_p \circ e_G = e_Q \circ \pi$ and
$\pi_p \circ s = \mathrm{id}_{Q_p}$; that is, the localized quotient map $\pi_p$ has a homomorphic
section.

Since $Q_p$ is nilpotent and $p$-local, $\pi_p$ is the unique homomorphism with
$\pi_p \circ e_G = e_Q \circ \pi$; since localizations are unique up to unique isomorphism, the
condition does not depend on the chosen localizations. -/
def SplitsAtPrime (p : ℕ) {G Q : Type} [Group G] [Group Q] (π : G →* Q) : Prop :=
  ∃ (Gp Qp : Type) (_ : Group Gp) (_ : Group Qp) (eG : G →* Gp) (eQ : Q →* Qp)
    (πp : Gp →* Qp) (s : Qp →* Gp), IsPLocalization p eG ∧ IsPLocalization p eQ ∧
      πp.comp eG = eQ.comp π ∧ πp.comp s = MonoidHom.id Qp

/-- **Hilton's splitting question for nilpotent extensions (Kourovka 12.93).** The proposition
that every extension of nilpotent groups with finitely generated quotient that splits at every
prime splits: for all nilpotent groups $N$, $G$ and $Q$ with $Q$ finitely generated, every
injective homomorphism $i \colon N \to G$ and every surjective homomorphism $\pi \colon G \to Q$
with $\operatorname{im} i = \ker \pi$ such that the extension splits at every prime $p$, there is
a homomorphism $s \colon Q \to G$ with $\pi \circ s = \mathrm{id}_Q$. -/
def nilpotentExtensionSplitsIfSplitsAtPrimes : Prop :=
  ∀ (N G Q : Type) [Group N] [Group G] [Group Q], Group.IsNilpotent N → Group.IsNilpotent G →
    Group.IsNilpotent Q → Group.FG Q → ∀ (i : N →* G) (π : G →* Q),
      Function.Injective i → Function.Surjective π → i.range = π.ker →
      (∀ p : ℕ, p.Prime → SplitsAtPrime p π) → ∃ s : Q →* G, π.comp s = MonoidHom.id Q

/--
**Nilpotent extensions that split at every prime need not split.** It is not true that every
extension of nilpotent groups with finitely generated quotient that splits at every prime splits:
there are nilpotent groups $N$, $G$ and $Q$ with $Q$ finitely generated, an injective homomorphism
$i \colon N \to G$ and a surjective homomorphism $\pi \colon G \to Q$ with $\operatorname{im} i =
\ker \pi$, such that the extension splits at every prime $p$ (for some $p$-localizations $G_p$
of $G$ and $Q_p$ of $Q$, the localized quotient map $\pi_p \colon G_p \to Q_p$ has a homomorphic
section) but there is no homomorphism $s \colon Q \to G$ with $\pi \circ s = \mathrm{id}_Q$.

Lorensen constructed such extensions in which $N$, $G$ and $Q$ are finitely generated and
torsion-free.

Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.93 (P. Hilton); resolution: K.
Lorensen, Nonsplit nilpotent group extensions that split at every prime, Math. Proc. Cambridge
Philos. Soc. 123 (1998), no. 2, 213-215, doi:10.1017/S0305004197002211, introduction (first page,
shown on Cambridge Core): examples of nilpotent group extensions which split at every p-localization
but fail to split, disproving Hilton's conjecture that any nilpotent group extension with finitely
generated quotient which splits at every prime must split; in both families of counterexamples the
groups are torsion-free and finitely generated. Kourovka Archive, Problem 12.93: 'No, not always',
https://doi.org/10.1017/S0305004197002211.
-/
public theorem_wanted nilpotentExtensionSplitsIfSplitsAtPrimes_refuted :
    ¬ nilpotentExtensionSplitsIfSplitsAtPrimes

end MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93Wanted
