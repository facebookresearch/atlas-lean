# Data, expression and combined complexity of query evaluation

This node collects the complexity measures of query evaluation and the data complexity of the relational
algebra.

## Expansion

A sound expansion has separate pages for:

1. **Measures.** Data complexity fixes the query and measures the cost of evaluation in the size of the
   instance; expression complexity fixes the instance and measures it in the size of the query; combined
   complexity measures it in both. Sizes are encoding lengths, at least $1$.
2. **Fixed-query bound.** For every fixed relational-algebra (or safe-range calculus) query $q$, possibly with
   constants, there are $k$ and $c$ depending only on $q$ such that $q(I)$ is computed in time
   $O\bigl((\lvert \mathrm{adom}(I) \rvert + 1)^k \cdot (\lVert I \rVert + 1)^c\bigr)$; hence data complexity is
   polynomial. This does not give polynomial combined complexity.
3. **Bounds for first-order logic.** On finite structures, the data complexity of first-order logic is in
   AC$^0$, and its combined and expression complexity are PSPACE-complete. Carrying these bounds to
   relational-calculus queries needs the active-domain and constants conventions of the calculus.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)
- [Relational algebra queries](../relational-algebra/expr.md)

## Sources

- Elements of Finite Model Theory (Libkin) — Leonid Libkin, Springer 2004; author's copy, Section 6.1 (data, expression and combined complexity, p. 87), Proposition 6.6 (time $O(\lVert \Phi \rVert \cdot \lVert \mathcal{A} \rVert^k)$ for a sentence of width $k$), Corollary 6.5 and Section 6.4 (AC$^0$), Theorem 6.16 and Corollary 6.17 (PSPACE-completeness). <https://www.cs.utoronto.ca/~libkin/fmt/fmt.pdf>
