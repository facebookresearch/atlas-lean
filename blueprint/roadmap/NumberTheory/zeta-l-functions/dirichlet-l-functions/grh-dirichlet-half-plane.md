# Generalized Riemann hypothesis for Dirichlet L-functions, half-plane form

Let $q \ge 1$ and let $\chi$ be a Dirichlet character modulo $q$, primitive or not. Then
$L(s, \chi) \ne 0$ for every complex number $s$ with $\operatorname{Re} s > 1/2$, except at
$s = 1$ when $\chi$ is principal, where $L(s, \chi)$ has a pole.

Here $L(s, \chi)$ is the meromorphic continuation of $\sum_{n \ge 1} \chi(n) n^{-s}$; it is entire
unless $\chi$ is principal. For the trivial character modulo $1$ it is the Riemann zeta function.

The statement follows from its case of primitive characters. A character $\chi$ modulo $q$ is induced by a primitive character $\chi^*$ modulo the conductor
$q^*$ of $\chi$, a divisor of $q$, and

$$
L(s, \chi) = L(s, \chi^*) \prod_{p \mid q} \bigl(1 - \chi^*(p) p^{-s}\bigr),
$$

where no factor of the finite product vanishes when $\operatorname{Re} s > 0$.

## Proof depends on

- [Primitive Dirichlet L-functions have no zero of real part greater than 1/2](primitive-dirichlet-l-functions-zero-free-half-plane.md)

## Sources

- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014), Conjecture 47 (generalised Riemann hypothesis: every zero of $L(\cdot, \chi)$, continued to $\operatorname{Re} s > 0$, has real part at most $1/2$), and equation (46) and Exercise 52 for the comparison of a character with its primitive inducing character, <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>.
- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`); the statement of this page is `LFunction_ne_zero_of_half_lt_re`. The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems, this one included (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
