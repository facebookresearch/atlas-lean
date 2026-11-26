# Andersen's analysis in cubic time

For a program of size $n$, the least solution of [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md) can be computed in time $O(n^3)$.

**Proof.** The numbers of abstract cells, the tokens, and of constraint variables are $O(n)$. The constraints have the forms $t \in x$ and $t \in x \implies y \subseteq z$ handled by the [cubic algorithm](../closure-analysis-0-cfa-and-the-cubic-algorithm.md), extended with unconditional inclusions $y \subseteq z$, so that algorithm computes the least solution in time $O(n^3)$.

The same bound holds for a specialized solver that represents each load $X_1 = {*}X_2$ by the single quantified constraint $\forall c \in [\![X_2]\!].\ [\![c]\!] \subseteq [\![X_1]\!]$, and each store likewise, and instantiates it whenever a new token reaches $[\![X_2]\!]$. Each pair of a token and a constraint variable enters its worklist at most once, at most $O(n^2)$ inclusion edges arise, and adding an edge propagates $O(n)$ tokens.

## Depends on

- [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md)

## Proof depends on

- [Closure analysis (0-CFA) and the cubic algorithm](../closure-analysis-0-cfa-and-the-cubic-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.2 (the constraints match the requirements of the cubic algorithm of Section 10.2 with the extension of Exercise 10.4) and Section 11.3 (the specialized points-to solver with quantified constraints and its $O(n^3)$ worst-case analysis).
