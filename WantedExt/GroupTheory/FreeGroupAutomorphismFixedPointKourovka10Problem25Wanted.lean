/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deciding fixed points of free group automorphisms (Kourovka Notebook Problem 10.25)

Kourovka Notebook, Archive of Solved Problems, Problem 10.25 (G. S. Makanin; well-known problem):
does there exist an algorithm which decides for a given automorphism of a free group whether this
automorphism has a non-trivial fixed point?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Partrec
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupAutomorphismFixedPointKourovka10Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.25 (G. S.
Makanin). UnsolvedMath record UM-00700640 (`KOU-10.25`), dataset ulamai/UnsolvedMath v1.8.0.

Free groups have finite rank `r`, and an automorphism is given by the images of the free generators
as words (lists of letters with inverse bits). Decidability is a computable function of the
generator images that answers correctly on every input defining an automorphism. The statement asks
for an algorithm for each rank; the algorithm of Bogopolski and Maslakova is uniform in the rank.
-/

/-- **Encoded words in a free group of finite rank.** A word of rank $r$ is a finite list of pairs
$(i, \varepsilon)$ with $i < r$ and $\varepsilon$ a Boolean. It encodes the element of the free
group $F_r$ of rank $r$ that is the product of its letters, where $(i, \mathrm{true})$ stands for
the $i$-th free generator and $(i, \mathrm{false})$ for its inverse. -/
abbrev Word (r : ℕ) : Type :=
  List (Fin r × Bool)

/-- **Endomorphism of a free group given by generator images.** Let $F_r$ be the free group on
generators $e_0, \dots, e_{r-1}$. Given, for each $i < r$, a word $u_i$ in these generators and
their inverses, this is the endomorphism of $F_r$ sending each $e_i$ to the element of $F_r$
represented by $u_i$. -/
def endo {r : ℕ} (img : Fin r → Word r) : FreeGroup (Fin r) →* FreeGroup (Fin r) :=
  FreeGroup.lift fun a => FreeGroup.mk (img a)

/-- **Decidability of fixed points of free group automorphisms (Kourovka 10.25).** The assertion
that for every natural number $r$ there is a computable function $f$ which takes the images of the
$r$ free generators of the free group $F_r$, each encoded as a word in the generators and their
inverses, and returns a Boolean, such that whenever the endomorphism $\varphi$ of $F_r$ sending each
generator to its image is bijective, $f$ returns true exactly when $\varphi(w) = w$ for some
$w \neq 1$ in $F_r$. -/
def automorphismFixedPointDecidable : Prop :=
  ∀ r : ℕ, ∃ f : (Fin r → Word r) → Bool, Computable f ∧
    ∀ img : Fin r → Word r, Function.Bijective (endo img) →
      (f img = true ↔ ∃ w : FreeGroup (Fin r), w ≠ 1 ∧ endo img w = w)

/--
**Fixed points of free group automorphisms are decidable (Kourovka 10.25).** For every natural
number $r$ there is a computable function $f$ which takes the images of the $r$ free generators of
the free group $F_r$, each encoded as a word in the generators and their inverses, and returns a
Boolean, such that whenever the endomorphism $\varphi$ of $F_r$ sending each generator to its image
is bijective, $f$ returns true exactly when $\varphi(w) = w$ for some $w \neq 1$ in $F_r$.

The Kourovka Archive answers Problem 10.25 "Yes, it does", citing Bogopolski and Maslakova (2016),
who give an algorithm computing a basis of the fixed subgroup of an automorphism of a free group of
finite rank; the automorphism has a non-trivial fixed point exactly when that basis is nonempty.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.25 (G. S.
Makanin); resolution: O. Bogopolski and O. Maslakova, Int. J. Algebra Comput. 26, no. 1 (2016),
29-67, algorithm computing a basis of the fixed subgroup of an automorphism of a free group of
finite rank; Kourovka Archive, Problem 10.25 ("Yes, it does").
-/
public theorem_wanted automorphismFixedPointDecidable_holds : automorphismFixedPointDecidable

end MathlibExt.GroupTheory.FreeGroupAutomorphismFixedPointKourovka10Problem25Wanted
