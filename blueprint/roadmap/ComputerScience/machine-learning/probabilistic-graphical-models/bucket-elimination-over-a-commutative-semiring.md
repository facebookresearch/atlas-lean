# Bucket elimination over a commutative semiring

Let $(K, \oplus, \otimes)$ be a commutative semiring, let $X_1, \dots, X_n$ be variables with finite domains
of size at most $k$, and let $\varphi_1, \dots, \varphi_m$ be factors, each a table from assignments of
its scope to $K$. For an ordering $d$ with induced width $w^*(d)$ of the interaction graph, bucket
elimination along $d$ (multiply the factors in a variable's bucket and sum that variable out) computes
$\bigoplus_{x_1, \dots, x_n} \bigotimes_j \varphi_j$, and, when the eliminated variables are all but a
chosen one, the corresponding single-variable marginal. Every factor it creates has scope of size at
most $w^*(d)$ (at most $w^*(d) + 1$ before summing out), so it uses
$O\bigl((m + n)\, k^{w^*(d) + 1}\bigr)$ semiring operations and table entries; the dependence on the number
$m$ of input factors cannot be dropped, since every input factor is read.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [Induced width of an ordering](induced-width-of-an-ordering.md)

## Sources

- R. Dechter, *Bucket elimination: a unifying framework for reasoning*, Artificial Intelligence 113 (1999) 41–85, Section 4: algorithm elim-bel (Fig. 17), Theorem 3 (it computes the marginal, p. 58) and Theorem 4 (time and space exponential in $w^*(d)$, p. 61), for the sum-product case. The proof uses only commutativity, associativity and distributivity, so it applies verbatim in any commutative semiring. <http://ics.uci.edu/~dechter/publications/r76A.pdf>
