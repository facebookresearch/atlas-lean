# The values of an anisotropic diagonal ternary form over $\mathbb{Q}_p$

Let $p$ be a prime
($p = 2$ included), let $a_1, a_2, a_3 \in \mathbb{Q}_p$ be nonzero, and suppose that
$f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$ has no zero in $\mathbb{Q}_p^3$ other than $(0, 0, 0)$.
Then for nonzero $a \in \mathbb{Q}_p$, $f(x) = a$ for some $x \in \mathbb{Q}_p^3$ if and only if
$-a \, a_1 a_2 a_3$ is not a square in $\mathbb{Q}_p$.

The proof derives this from the binary and ternary criteria
(`padicHilbertSymbol.exists_mul_sq_add_mul_sq_eq_iff`,
`padicHilbertSymbol.exists_ternary_eq_zero_iff`; A. V. Sutherland, *18.782 Introduction to
Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, Lemma 11.3 and Corollary 11.4, p. 1), the
bilinearity of the symbol and its nondegeneracy (`padicHilbertSymbol.forall_eq_one_iff_isSquare`),
by a character argument on the square classes.
