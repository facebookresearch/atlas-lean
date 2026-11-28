# The values of an anisotropic diagonal ternary form over $\mathbb{R}$

Let
$a_1, a_2, a_3$ be nonzero real numbers and suppose that $f = a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2$
has no zero in $\mathbb{R}^3$ other than $(0, 0, 0)$. Then for a nonzero real number $a$,
$f(x) = a$ for some $x \in \mathbb{R}^3$ if and only if $-a \, a_1 a_2 a_3$ is not a square in
$\mathbb{R}$.

The proof is the one of `padicHilbertSymbol.exists_ternary_eq_iff_not_isSquare`, with the
bilinearity and nondegeneracy of the real symbol read off the sign rule
`realHilbertSymbol.eq_neg_one_iff_both_neg`.
