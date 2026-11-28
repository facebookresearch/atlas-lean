# Representation by diagonal ternary forms over $\mathbb{Q}_p$

Let $p$ be a prime
($p = 2$ included), let $a_1, a_2, a_3 \in \mathbb{Q}_p$ be nonzero, let
$f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ and let $d = a_1 a_2 a_3$. Then:

1. $f$ has a zero in $\mathbb{Q}_p^3$ other than $(0, 0, 0)$ if and only if the $p$-adic Hilbert
   symbol $(-a_1 a_2, -a_1 a_3)_p$ equals $1$;
2. for nonzero $a \in \mathbb{Q}_p$, $f(x) = a$ for some $x \in \mathbb{Q}_p^3$ if and only if $f$
   has such a zero or $-a d$ is not a square in $\mathbb{Q}_p$.

Part 1 is `hilbertSymbol.exists_ternary_eq_zero_iff`; part 2 combines the fact that a diagonal
ternary form with a nonzero zero takes every value with
`padicHilbertSymbol.exists_ternary_eq_iff_not_isSquare`. The proof derives both from
A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 11,
Lemma 11.3 and Corollary 11.4, p. 1, and the nondegeneracy of the symbol.
