# Dyadic Fefferman–Stein vector-valued maximal inequality

For $1 < p, q < \infty$ there is a finite constant $C$, depending only on $p$ and $q$, such that for every sequence of measurable functions $f_i \colon \mathbb{R} \to \mathbb{R}$,

$$\int_{\mathbb{R}} \Big(\sum_i (M_d f_i)^q\Big)^{p/q} \le C \int_{\mathbb{R}} \Big(\sum_i |f_i|^q\Big)^{p/q},$$

that is $\|(M_d f_i)_i\|_{L^p(\ell^q)} \le C^{1/p} \|(f_i)_i\|_{L^p(\ell^q)}$, where $M_d$ is the [dyadic maximal function](dyadic-maximal-function.md).

This is T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 4.9, with $\mu$ the Lebesgue measure on $\mathbb{R}$, the dyadic form of the inequality of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, for the Hardy–Littlewood maximal function on $\mathbb{R}^n$ (Hytönen's Exercise 4.14 derives the usual form from the dyadic one). The statement here is the one-dimensional dyadic case, weaker than the original. The case $p = q$ is the [scalar $L^p$ bound](lintegral-rpow-dyadic-maximal-function-l.md) summed over $i$; for $q = \infty$ (not covered here) the inequality reduces to the scalar bound applied to $\sup_i |f_i|$.

## Background

- [$L^p$ bound for the dyadic maximal function](lintegral-rpow-dyadic-maximal-function-l.md): the proved scalar case, which gives the case $p = q$.
- [Calderón–Zygmund decomposition, dyadic form](calderon-zygmund.md): the decomposition of the $\ell^q$-valued function used in the original weak type (1,1) proof.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 4.9 (a secondary source).
- C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115 (original; not read for this page).
