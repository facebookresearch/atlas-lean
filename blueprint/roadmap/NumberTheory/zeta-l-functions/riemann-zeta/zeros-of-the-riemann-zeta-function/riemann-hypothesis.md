# Riemann hypothesis

Every nontrivial zero of the Riemann zeta function has real part $1/2$: if $\zeta(s) = 0$ and $s$
is not one of the trivial zeros $-2, -4, -6, \dots$, then $\operatorname{Re} s = 1/2$.

Here $\zeta$ is the meromorphic continuation of $\sum_{n \ge 1} n^{-s}$ to the complex plane; its
only pole is at $s = 1$. Equivalently, every zero of the Riemann $\xi$ function
$\xi(s) = \tfrac12 s (s - 1) \pi^{-s/2} \Gamma(s/2) \zeta(s)$ lies on the line
$\operatorname{Re} s = 1/2$; this is Riemann's formulation, that all zeros of
$t \mapsto \xi(1/2 + it)$ are real.

Alpöge's proof, cited below, derives the statement from the half-plane form of the generalized
Riemann hypothesis for Dirichlet L-functions, applied to the trivial character modulo $1$, whose
L-function is $\zeta$: no zero of $\zeta$ has real part greater than $1/2$. A zero $\rho$ with
real part less than $1/2$ that is not a trivial zero is not a non-positive integer, since
$\zeta(0) = -1/2$ and $\zeta$ does not vanish at the negative odd integers. The functional
equation

$$
\zeta(1 - s) = 2 (2\pi)^{-s} \Gamma(s) \cos(\pi s / 2) \zeta(s) \qquad (s \ne 1,\ s \ne 0, -1, -2, \dots)
$$

at $s = \rho$ then gives $\zeta(1 - \rho) = 0$, a zero of real part greater than $1/2$.

## Proof depends on

- [Generalized Riemann hypothesis for Dirichlet L-functions, half-plane form](../../dirichlet-l-functions/zeros-of-dirichlet-l-functions/grh-dirichlet-half-plane.md)

## Sources

- E. Bombieri, *Problems of the Millennium: the Riemann Hypothesis*, official problem description, Clay Mathematics Institute, §I, <https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf>: the statement "The nontrivial zeros of $\zeta(s)$ have real part equal to $1/2$", with the trivial zeros $-2, -4, \dots$, and B. Riemann's original formulation (1859) that all zeros of $\xi(t)$, $s = 1/2 + it$, are real, quoted there.
- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>), with Mathlib's `RiemannHypothesis` as the statement of this page. Statement and proof certified by the Lean and Mathlib communities in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>. The library has no licence, so ATLAS has no Lean proof.
