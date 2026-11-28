# A diagonal ternary form has a nonzero zero exactly when $(-a_1 a_2, -a_1 a_3) = 1$

Let
$F$ be a field in which $2 \neq 0$ and let $a_1, a_2, a_3 \in F$ be nonzero. Then
$a_1 x_1^2 + a_2 x_2^2 + a_3 x_3^2 = 0$ for some $(x_1, x_2, x_3) \in F^3$ other than $(0, 0, 0)$
if and only if the Hilbert symbol $(-a_1 a_2, -a_1 a_3)_F$ equals $1$.

The fields $\mathbb{R}$ and $\mathbb{Q}_p$ ($p = 2$ included) are the cases of interest; the
statement holds over every field with $2 \neq 0$. The proof multiplies the form by $a_1$, which
turns it into $(a_1 x_1)^2 + a_1 a_2 x_2^2 + a_1 a_3 x_3^2$, and applies
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`, the equivalence (i) ⇔ (ii) of A. V. Sutherland,
*18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture 10, Lemma 10.2, p. 1 (stated
there over $\mathbb{Q}_p$, $p \le \infty$). The reduction of a diagonal ternary form to
$z^2 - a x^2 - b y^2$ is written out here.
