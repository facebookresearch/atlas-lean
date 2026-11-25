# Closure analysis (0-CFA) and the cubic algorithm

**Closure analysis.** Consider untyped lambda terms $E ::= \lambda X.\, E \mid X \mid E\,E$ in which all bound variables are distinct. Closure analysis approximates, for every subterm, the set of abstractions to which it may evaluate. Each abstraction $\lambda X.\, E$ is represented by a token $\lambda X$. Every node $v$ of the syntax tree gets a constraint variable $[\![v]\!]$ ranging over sets of tokens, subject to the following constraints:

- for every abstraction, $\lambda X \in [\![\lambda X.\, E]\!]$;
- for every application $E_1\,E_2$ and every abstraction $\lambda X.\, E$, the conditional constraint

$$\lambda X \in [\![E_1]\!] \implies [\![E_2]\!] \subseteq [\![X]\!] \ \wedge\ [\![E]\!] \subseteq [\![E_1\,E_2]\!].$$

It states that the argument may flow into the formal parameter and that the body's values are among the results of the call.

**The cubic algorithm.** Let constraints of the forms $t \in x$ and $t \in x \implies y \subseteq z$ be given over a finite set of tokens and a finite set of variables. Solutions are closed under intersection, so a unique least solution exists. The following algorithm computes it in time $O(n^3)$ for a program of size $n$, when the numbers of tokens and variables are $O(n)$.
- Keep a graph of inclusion edges between variables, the current solution of each variable, and the pending conditional constraints for each pair of a variable and a token.
- Adding a token to a variable propagates it along the edges and triggers the pending conditional constraints for that token, which add edges.

Closure analysis is an instance, so its least solution is computed in cubic time.

## Depends on

- [Monotone frameworks and the work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, <https://cs.au.dk/~amoeller/spa/>, Section 10.1 (closure analysis for the λ-calculus and its constraints), Section 10.2 (the cubic algorithm, Exercise 10.2 on the unique least solution, and the $O(n^3)$ analysis).
