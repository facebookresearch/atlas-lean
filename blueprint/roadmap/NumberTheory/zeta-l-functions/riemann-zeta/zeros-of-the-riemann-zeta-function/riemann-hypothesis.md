# Riemann hypothesis

Every nontrivial zero of the Riemann zeta function has real part $1/2$: if $\zeta(s) = 0$ and $s$
is not one of the trivial zeros $-2, -4, -6, \dots$, then $\operatorname{Re} s = 1/2$.

Here $\zeta$ is the meromorphic continuation of $\sum_{n \ge 1} n^{-s}$ to the complex plane; its
only pole is at $s = 1$. Equivalently, every zero of the Riemann $\xi$ function lies on the line
$\operatorname{Re} s = 1/2$; this is Riemann's formulation, that all zeros of
$t \mapsto \xi(1/2 + it)$ are real. Here $\xi(s) = \tfrac12 s (s - 1) \Lambda(s)$, where
$\Lambda(s) = \pi^{-s/2} \Gamma(s/2) \zeta(s)$ is the completed zeta function: as a meromorphic
function its only poles are simple poles at $s = 0$ and $s = 1$, since the poles of $\Gamma(s/2)$
at $-2, -4, \dots$ cancel the trivial zeros of $\zeta$. So $\xi$ is entire, with $\xi(0) = \xi(1) = 1/2$,
and its zeros are the nontrivial zeros of $\zeta$.

The statement follows from the half-plane form of the generalized Riemann hypothesis for Dirichlet
L-functions, applied to the trivial character modulo $1$, whose L-function is $\zeta$: no zero of $\zeta$ has real part greater than $1/2$. A zero $\rho$ with
real part less than $1/2$ that is not a trivial zero is not a non-positive integer, since
$\zeta(0) = -1/2$ and $\zeta$ does not vanish at the negative odd integers. The functional
equation

$$
\zeta(1 - s) = 2 (2\pi)^{-s} \Gamma(s) \cos(\pi s / 2) \zeta(s) \qquad (s \ne 1,\ s \ne 0, -1, -2, \dots)
$$

at $s = \rho$ then gives $\zeta(1 - \rho) = 0$, a zero of real part greater than $1/2$.

## Depends on

- [Statement of the Riemann hypothesis](../riemann-hypothesis-statement.md)

## Proof depends on

- [Generalized Riemann hypothesis for Dirichlet L-functions, half-plane form](../../dirichlet-l-functions/grh-dirichlet-half-plane.md)

## Sources

- E. Bombieri, *Problems of the Millennium: the Riemann Hypothesis*, official problem description, Clay Mathematics Institute, §I, <https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf>: the statement "The nontrivial zeros of $\zeta(s)$ have real part equal to $1/2$", with the trivial zeros $-2, -4, \dots$, and B. Riemann's original formulation (1859) that all zeros of $\xi(t)$, $s = 1/2 + it$, are real, quoted there.
- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) whose five main theorems are two forms of the Riemann hypothesis (`riemannHypothesis`, `riemannZeta_eq_zero_re`) and three forms of the generalized Riemann hypothesis for Dirichlet L-functions (`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`); its theorem `riemannHypothesis` proves Mathlib's `RiemannHypothesis`, the statement of this page. The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
