# Generalized Riemann hypothesis for Dirichlet L-functions, critical-strip form

Let $\chi$ be a Dirichlet character, primitive or not. Every zero $\rho$ of $L(s, \chi)$ with
$0 < \operatorname{Re} \rho < 1$ has $\operatorname{Re} \rho = 1/2$.

Here $L(s, \chi)$ is the meromorphic continuation of $\sum_{n \ge 1} \chi(n) n^{-s}$. When $\chi$ is
imprimitive, $L(s, \chi)$ is the L-function of its primitive inducing character $\chi^*$ times a
finite product of factors $1 - \chi^*(p) p^{-s}$, whose zeros lie on the line
$\operatorname{Re} s = 0$, outside the strip.

The statement follows from the half-plane form, which excludes the zeros of real part greater than $1/2$. A zero $\rho$ of $L(\cdot, \chi)$ with
$0 < \operatorname{Re} \rho < 1/2$ is a zero of $L(\cdot, \chi^*)$. Write $q^*$ for the conductor
and $\mathfrak a \in \{0, 1\}$ for the parity of $\chi^*$, and
$\Lambda(s, \chi^*) = (q^*/\pi)^{(s + \mathfrak a)/2} \Gamma\bigl((s + \mathfrak a)/2\bigr) L(s, \chi^*)$
for its completed L-function. The functional equation of the primitive character $\chi^*$ gives
$\Lambda(1 - s, \overline{\chi^*})$ as $\Lambda(s, \chi^*)$ times a factor of absolute value $1$,
and the Gamma factors are finite and non-zero for real parts in $(0, 1)$. So $1 - \rho$ is a zero
of $L(\cdot, \overline{\chi^*})$, of real part greater than $1/2$, which the half-plane form
excludes.

## Proof depends on

- [Generalized Riemann hypothesis for Dirichlet L-functions, half-plane form](grh-dirichlet-half-plane.md)

## Sources

- T. Tao, *254A, Notes 2: Complex-analytic multiplicative number theory* (2014), Conjecture 47 (the generalised Riemann hypothesis in its half-plane form) and Exercise 52 (primitive inducing characters), <https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/>.
- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`); the statement of this page is `LFunction_eq_zero_re`, and its case of primitive characters is `LFunction_eq_zero_re_of_isPrimitive`. The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems, these two included (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
