# Dadush–Tiwari: cutting planes refute Tseitin formulas in quasi-polynomial size

Let $H = (V, E)$ be a graph with $n$ vertices and maximum degree $\Delta$, and let $\ell : V \to \{0,1\}$ be a charge function of odd total weight. The Tseitin formula of $(H, \ell)$, the CNF of the parity constraints $\sum_{e \ni v} x_e \equiv \ell(v) \pmod 2$ over one variable per edge, has a cutting planes refutation of length $2^{\Delta} (n\Delta)^{O(\log n)}$. For bounded-degree graphs this is quasi-polynomial, refuting the conjecture that Tseitin formulas on expanders require exponential cutting planes length.

More generally, call a branching proof **enumerative** if at every node it branches on all integer values $b$ of a single integer linear form $a \cdot x$ over the current relaxation, each child adding the equality $a \cdot x = b$. Every enumerative branching proof $T$ of integer infeasibility of a compact convex set $K \subseteq \mathbb{R}^n$ converts into a sequence of at most $2|T| - 1$ Chvátal-Gomory cuts whose application empties $K$.

## Proof sketch

The quasi-polynomial stabbing planes refutation of Tseitin formulas is enumerative: it only branches on the exact number of true edges crossing a cut and, at the end, on the values of the edges at a single vertex. To serialize an enumerative proof, start at the root with branching form $a$ and push the hyperplane $a \cdot x = b$ backwards through $K$, starting from the maximum of $a \cdot x$ over $K$. A Chvátal-Gomory cut along $a$ first rounds the maximum down to an integer $b$. The subtree of the child labelled $a \cdot x = b$ is a valid enumerative proof for the face $K \cap \{a \cdot x = b\}$; recursively it yields cuts that empty this face, and a lifting lemma for Chvátal-Gomory cuts lifts each of them from the face to a cut on $K$ (adding a large multiple of $a$) with the same effect on the face. Once the face is removed, the next cut along $a$ lowers $b$ by one, and the process continues until $b$ drops below the minimum of $a \cdot x$ over $K$. Counting cuts gives at most $2|T| - 1$.

## Proof depends on

- [Stabbing planes refute Tseitin formulas in quasi-polynomial size](sp-tseitin-quasipoly.md)

## Sources

- D. Dadush, S. Tiwari, "On the complexity of branching proofs", CCC (2020), LIPIcs 169, Art. 34, doi:10.4230/LIPIcs.CCC.2020.34, arXiv:2006.04124 (Theorems 3 and 4, Lemmas 20 and 30, Section 4.1).
