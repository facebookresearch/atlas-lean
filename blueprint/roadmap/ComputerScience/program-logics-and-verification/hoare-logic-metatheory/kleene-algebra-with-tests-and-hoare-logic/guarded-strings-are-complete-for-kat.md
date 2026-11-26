# Guarded strings are complete for Kleene algebra with tests

Let $\Sigma$ be a finite set of primitive actions and $B$ a finite set of primitive tests, and let $\mathrm{At}$ be the set of *atoms*, the conjunctions that contain each primitive test or its complement. A *guarded string* is a word $\alpha_0 p_1 \alpha_1 p_2 \cdots p_n \alpha_n$ with $n \ge 0$, atoms $\alpha_i$ and actions $p_i$. Each KAT term $p$ over $\Sigma$ and $B$ denotes a set $G(p)$ of guarded strings: a primitive action $p$ denotes $\{\alpha p \beta\}$ over all atoms, a test $b$ the atoms below it, $+$ union, $\cdot$ the fusion product that joins $x\alpha$ and $\alpha y$ to $x\alpha y$, and ${}^\ast$ its iteration. Then, for all terms $p, q$, the equation $p = q$ holds in every [Kleene algebra with tests](kleene-algebras-with-tests.md) if and only if $G(p) = G(q)$. Consequently the free KAT is the algebra of regular sets of guarded strings, and KAT is complete for the equational theory of relational models.

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)

## Sources

- D. Kozen, "On Hoare logic and Kleene algebra with tests", *ACM Transactions on Computational Logic* 1(1), 2000, author copy <https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf>, Section 2.3 (the regular sets of guarded strings form the free KAT; completeness for relational models, after Kozen and Smith, *CSL 1996*) and Section 4 (guarded strings, their product and the standard interpretation $G$).
- E. Cohen, D. Kozen and F. Smith, *The Complexity of Kleene Algebra with Tests*, technical report, Cornell University, 1996, <https://www.cs.cornell.edu/~kozen/Papers/ckat.pdf>, Section 3, Theorem 4.
