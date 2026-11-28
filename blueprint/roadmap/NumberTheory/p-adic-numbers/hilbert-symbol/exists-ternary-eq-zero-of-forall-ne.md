# Ternary forms with a nonzero zero at all places but one

Let $a_1, a_2, a_3$ be nonzero
rational numbers and let $v_0$ be a place of $\mathbb{Q}$. If
$a_1 x^2 + a_2 y^2 + a_3 z^2 = 0$ has a solution $(x, y, z) \neq (0, 0, 0)$ in $\mathbb{Q}_v^3$
for every place $v \neq v_0$ of $\mathbb{Q}$, then it has such a solution in $\mathbb{Q}_v^3$ for
every place $v$ of $\mathbb{Q}$, $v_0$ included. Here $\mathbb{Q}_v$ is $\mathbb{R}$ at the
infinite place and $\mathbb{Q}_p$ at the place of a prime $p$.

## Sources

- A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, Corollary 11.5 and its proof, p. 2, for the nondegenerate case; Sutherland's proof uses the product formula for Hilbert symbols and Corollary 11.4. Here the criterion at each place is `hilbertSymbol.exists_ternary_eq_zero_iff`, and the product formula is `Rat.hilbertSymbol_product_formula`.
