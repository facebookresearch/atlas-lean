# Extended resolution

Extended resolution is resolution together with Tseitin's clausal extension rule, which introduces a fresh variable $x$ with the three clauses expressing $x \leftrightarrow (a \wedge b)$ for literals $a,b$. It is a sound and complete refutation system for CNF formulas.

Let $F$ be a CNF formula. An *extended resolution* (ER) *derivation* from $F$ is a sequence of clauses, each of which is a clause of $F$, a resolvent $B \vee C$ of earlier clauses $B \vee x$ and $C \vee \neg x$, or one of the three clauses

$$
\neg x \vee a, \qquad \neg x \vee b, \qquad \neg a \vee \neg b \vee x
$$

introduced together by the *extension rule*, where $a,b$ are literals and $x$ is a new variable: $x$ does not occur in $F$ nor earlier in the derivation. An ER *refutation* of $F$ is a derivation of the empty clause.

Facts recorded in the sources:

- The extension rule preserves satisfiability: a satisfying assignment of the current clauses extends to $x$ by giving $x$ the value of $a \wedge b$. Hence extended resolution is sound and, containing resolution, complete.
- Resolution does not p-simulate extended resolution: the pigeonhole formulas have polynomial-size extended resolution refutations (Cook and Reckhow) but require exponential-size resolution refutations (Haken).
- Iterating the clausal rule with several new variables simulates the general extension rule $x \leftrightarrow \varphi$ for an arbitrary formula $\varphi$.

## Expansion

The extension rule names the output of an AND gate; chaining such names lets a resolution refutation reason about the values of arbitrary Boolean circuits on the input variables, which is the source of its strength. The lower bound for resolution used in the separation is [Haken's lower bound for the pigeonhole principle](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md). In SAT solving the same clauses can be added one at a time as RAT clauses, which is how DRAT proof logging simulates extended resolution.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.8: the general extension rule (7.69), the clausal extension rule (7.70) expressing $x \leftrightarrow (a\wedge b)$, soundness, and the exponential separation from resolution via the pigeonhole principle).
- Sam Buss and Neil Thapen, "DRAT and propagation redundancy proofs without new variables", *Logical Methods in Computer Science* 17(2):12, 2021, doi:10.23638/LMCS-17(2:12)2021, arXiv:1909.00520v6 (Section 2.1: extension clauses expressing $x \leftrightarrow (p \wedge q)$ for a new variable $x$; Example 1.8).
