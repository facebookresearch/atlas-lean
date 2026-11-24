# Interior $H^2$ regularity

Let $U \subseteq \mathbb{R}^n$ be bounded and open. Assume $a^{ij} = a^{ji}$, $a^{ij} \in C^1(U)$
and bounded on $U$, $b^i, c \in L^\infty(U)$, and uniform ellipticity
$\theta |\xi|^2 \le \sum a^{ij}(x) \xi_i \xi_j$ on $U$ for some $\theta > 0$. For every open $V$
with $\overline V$ compact and contained in $U$ ($V \subset\subset U$) there is a constant $C$,
depending only on $U$, $V$ and the coefficients, such that every weak solution $u \in H^1(U)$ of
$Lu = f$ with $f \in L^2(U)$ has weak derivatives up to order two on $V$, in $L^2(V)$, and

$$\|u\|_{L^2(V)} + \sum_i \|\partial_i u\|_{L^2(V)} + \sum_{i,j} \|\partial_j \partial_i u\|_{L^2(V)}
\le C \big( \|f\|_{L^2(U)} + \|u\|_{L^2(U)} \big).$$

So $u \in H^2_{\mathrm{loc}}(U)$. The left side is a norm equivalent to the $H^2(V)$ norm; since $C$
is existential, the statement is equivalent to the source's estimate for
$\|u\|_{H^2(V)}$. Ellipticity is assumed at every point of $U$ rather than almost everywhere,
which is equivalent for continuous coefficients. The classical proof uses difference quotients.
All the hypotheses hold for the
[coefficients of the Laplacian on nested balls](interior-h2-regularity-hypotheses-laplac.md),
so the statement is not vacuous.

## Background

- [Weak solution of a divergence-form elliptic equation](is-weak-solution-on.md): the hypothesis.
- [Weak partial derivative on an open set](is-weak-partial-deriv-on.md): the second derivatives in
  the conclusion.

## Sources

- P. Howard, MATH 612 lecture slides, Texas A&M University, Spring 2020: [Interior $H^2$ regularity](https://people.tamu.edu/~phoward/m612/s20/elliptic7.pdf), Theorem 6.3.1, the interior $H^2$-regularity theorem of §6.3.1 of L. C. Evans, *Partial
  Differential Equations*, 2nd ed. (cited through the slides).
