# Second-order unification problems

Second-order unification asks whether finitely many equations between terms containing function variables, and possibly individual variables, can be solved by substituting first-order terms for the individual variables and lambda-abstractions of first-order terms for the function variables.

**Terms.** Fix a signature $\Sigma$ of function symbols with arities (arity $0$ for constants), a countably infinite set of *individual variables* $x, y, z, \dots$ and, disjoint from it, a countably infinite set of *function variables* $F, G, H, \dots$, each with an arity $n > 0$. Terms are built from individual variables by the function symbols and the function variables, applied to as many terms as their arity. A term is *first-order* if it contains no function variable and *ground* if it is first-order and contains no individual variable.

**Substitutions and unifiers.** A substitution maps finitely many function variables $F$ of arity $n$ to $\lambda y_1 \dots y_n.\, t$ with $t$ a first-order term whose individual variables are among $y_1, \dots, y_n$, and finitely many individual variables to terms; applying it to a term substitutes and then $\beta$-reduces, so that the result contains no lambda. A *second-order unification problem* is a finite set of equations $u =^? v$ between terms; a *unifier* is a substitution $\sigma$, mapping all function variables of the problem to such abstractions, with $u\sigma = v\sigma$ (syntactic equality) for each equation. For a set $E$ of equational axioms, *second-order $E$-unification* replaces syntactic equality by equality modulo $E$.

**Ground second-order problems.** A term is *$n$-second-order ground* if it contains no individual variable and its function variables all have arity $n$. An *$n$-second-order ground $\mathcal{A}$-unification problem* ($n$-ASOGU problem) is a finite set of equations $u =^? v$ between $n$-second-order ground terms in which exactly one function variable $F$ occurs (possibly many times), together with a nonempty finite set $\mathcal{A}$ of associativity axioms $f(x, f(y,z)) \approx f(f(x,y),z)$ for some binary symbols $f$; a unifier maps $F$ to an abstraction as above so that $u\sigma$ and $v\sigma$ are equal modulo $\mathcal{A}$ for every equation.

## Depends on

- [E-unification problems](../../first-order-logic/equational-unification/equational-unification-problems.md)
- [β-reduction](../../../ComputerScience/type-systems-and-lambda-calculi/untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

None.

## Expansion

First-order unification is the case without function variables, and it is decidable. In the simply typed λ-calculus, second-order unification is [higher-order unification](higher-order-unification-and-its-order.md) restricted to variables of order at most two; function variables applied to first-order terms are its usual presentation. Second-order unification was proved undecidable by Goldfarb, strengthening Huet's undecidability of higher-order unification; much later work determines which restrictions on the numbers of second-order and first-order variables restore decidability. Monadic second-order unification, second-order linear unification, bounded second-order unification and context unification are decidable.

## Sources

- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:10.46298/lmcs-22(2:3)2026; read as arXiv:2404.10616v10, <https://arxiv.org/abs/2404.10616v10>: Section 2 (terms, $n$-second-order ground terms and problems, substitutions, unifiers, equational theories and $n$-ASOGU problems) and Section 1 (the history of the problem).
