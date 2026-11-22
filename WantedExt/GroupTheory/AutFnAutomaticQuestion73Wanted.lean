/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AutFnAutomaticQuestion73Wanted

/-!
# Question 7.3 — Is Aut(Fn) automatic for n > 3? (AMR-109-0302)

Stable source identifiers:
- Source list: Farb - Problems on Mapping Class Groups and Related Topics
- Source item: Question 7.3, PDF page 339
- Source URL: https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf

Clause list (every hypothesis, side condition, and quantifier domain in the source):
1. `n : ℕ`: rank parameter.
2. `3 < n`: strict threshold from the source ("n > 3"), open at 3.
3. `Fn = FreeGroup (Fin n)`: free group on `n` generators (Mathlib `FreeGroup`).
4. `Aut(Fn) = MulAut (FreeGroup (Fin n))`: automorphism group (Mathlib `MulAut`).
5. `automatic`: standard automatic-group property applied to `Aut(Fn)`.
6. Claim form: question whether (5) holds for all `n` satisfying (1)-(2); posed as open
   in the source, since resolved (see the entry metadata); no proof in this repository.
-/

/-- **Automatic group.** A group $G$ is automatic if there are a finite alphabet $A$, an
involution $\iota$ of $A$, a map $\mathrm{ev} \colon A \to G$ with
$\mathrm{ev}(\iota(a)) = \mathrm{ev}(a)^{-1}$ for all $a \in A$, a language $L$ of words over $A$
that is exactly the set of words accepted by some deterministic finite automaton, and a natural
number $k$ with the following properties. Write $\overline{w} \in G$ for the product of the
images under $\mathrm{ev}$ of the letters of a word $w$, and $w(t)$ for the prefix of $w$ of
length $t$ (all of $w$ if $t$ exceeds its length). Every element of $G$ equals $\overline{w}$ for
some $w \in L$. For all $u, v \in L$ such that $\overline{u} = \overline{v}$, or
$\overline{u}\,\mathrm{ev}(a) = \overline{v}$ for some letter $a$, and for every $t \in \mathbb{N}$,
the element $\overline{u(t)}^{-1}\,\overline{v(t)}$ equals $\overline{w}$ for some word $w$ of
length at most $k$.

This is the fellow-traveller characterization of automatic groups (Epstein et al., Word
Processing in Groups, Theorem 2.3.5).

Source: Question 7.3 [AMR-109-0302], Farb - Problems on Mapping Class Groups and Related Topics,
PDF p. 339, https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf. -/
def IsAutomaticGroup (G : Type*) [Group G] : Prop :=
  ∃ (A : Type) (_ : Fintype A) (inv : A → A),
    (∀ a, inv (inv a) = a) ∧
    ∃ (eval : A → G),
      (∀ a, eval (inv a) = (eval a)⁻¹) ∧
      ∃ (L : List A → Prop),
        (∃ (State : Type) (_ : Fintype State) (start : State)
            (step : State → A → State) (accept : State → Bool),
            ∀ w : List A, L w ↔ accept (List.foldl step start w) = true) ∧
        (∀ g : G, ∃ w : List A, L w ∧ List.prod (List.map eval w) = g) ∧
        ∃ k : ℕ,
          (∀ u v : List A, L u → L v →
              List.prod (List.map eval u) = List.prod (List.map eval v) →
              ∀ t : ℕ, ∃ w : List A,
                List.length w ≤ k ∧
                  (List.prod (List.map eval (List.take t u)))⁻¹ *
                    List.prod (List.map eval (List.take t v)) =
                    List.prod (List.map eval w)) ∧
          ∀ u v : List A, L u → L v → ∀ a : A,
            List.prod (List.map eval u) * eval a =
              List.prod (List.map eval v) →
            ∀ t : ℕ, ∃ w : List A,
              List.length w ≤ k ∧
                (List.prod (List.map eval (List.take t u)))⁻¹ *
                  List.prod (List.map eval (List.take t v)) =
                  List.prod (List.map eval w)

/-- **Automaticity of automorphism groups of free groups (Farb's Question 7.3).** The statement
that for every natural number $n > 3$ the automorphism group $\mathrm{Aut}(F_n)$ of the free group
$F_n$ on $n$ generators is an automatic group.

Source: Question 7.3 [AMR-109-0302], Farb - Problems on Mapping Class Groups and Related Topics,
PDF p. 339, https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf. -/
def conjecture : Prop :=
  ∀ n : ℕ, 3 < n → IsAutomaticGroup (MulAut (FreeGroup (Fin n)))

/--
**Negative answer to Farb's Question 7.3.** It is not the case that for every natural number
$n > 3$ the automorphism group $\mathrm{Aut}(F_n)$ of the free group on $n$ generators is
automatic.

Bridson and Vogtmann, with Handel and Mosher, proved more: $\mathrm{Aut}(F_n)$ has exponential
Dehn function for every $n \ge 3$, while automatic groups have at most quadratic Dehn functions
(Epstein et al.), so $\mathrm{Aut}(F_n)$ is automatic for no $n \ge 3$.

Source: M. R. Bridson, K. Vogtmann, The Dehn functions of Out(F_n) and Aut(F_n), Annales de
l'Institut Fourier 62(5) (2012) 1811-1817, arXiv:1011.1506, https://arxiv.org/abs/1011.1506.
Moved from `OpenConjectures/GroupTheory/AutFnAutomaticQuestion73`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.AutFnAutomaticQuestion73Wanted
