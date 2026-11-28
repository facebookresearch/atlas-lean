# Number of units modulo an ideal, as a product over its prime factors

Let $S$ be a
Dedekind domain that is a finite free $\mathbb{Z}$-module (for example the ring of integers of a
number field) and let $I \neq 0$ be an ideal of $S$, with factorisation
$I = \prod_{\mathfrak{p}} \mathfrak{p}^{e_{\mathfrak{p}}}$ into prime ideals
(`UniqueFactorizationMonoid.normalizedFactors`, with multiplicities $e_{\mathfrak{p}}$). Then the
unit group of $S/I$ has

$$\prod_{\mathfrak{p} \mid I}
\bigl(N(\mathfrak{p})^{e_{\mathfrak{p}}} - N(\mathfrak{p})^{e_{\mathfrak{p}} - 1}\bigr)$$

elements, where $N(\mathfrak{p}) = \#(S/\mathfrak{p})$ is the absolute norm (`Ideal.absNorm`)
of the nonzero prime ideal $\mathfrak{p}$.

This is the Chinese remainder theorem reduction to prime powers of F. Keune, *Number Fields*,
2023, pp. 135–136, combined with `Ideal.natCard_units_quotient_pow` (Keune, Chapter 6,
Exercise 1(ii), p. 141).
