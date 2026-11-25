# Moment closure for polynomial-preserving generators

Let $E\subseteq\mathbb R^d$ be compact, $n\ge0$, and let $\mathcal P_n$ be the space of real polynomials of degree at most $n$ restricted to $E$, with a basis $p_1,\ldots,p_r$. Let $A$ be an operator whose domain contains $\mathcal P_n$ and which maps $\mathcal P_n$ into itself: $Ap_i=\sum_jc_{ij}p_j$ on $E$ for a real $r\times r$ matrix $C=(c_{ij})$. If $X$ solves the [martingale problem](martingale-problems-generic-definition.md) for $A$ (with càdlàg paths) and $m(t)=\bigl(\mathbb E\,p_1(X_t),\ldots,\mathbb E\,p_r(X_t)\bigr)^{\top}$, then

$$m(t)=m(0)+\int_0^tC\,m(s)\,ds,\qquad\text{hence}\qquad m(t)=e^{tC}m(0)\quad(t\ge0).$$

In particular, if $A$ maps polynomials of degree at most $1$ into themselves, the mean $\mathbb E X_t$ solves a linear ordinary differential equation. For the neutral Wright–Fisher generator $Af=\tfrac12x(1-x)f''$ on $[0,1]$ and the heterozygosity $h(x)=2x(1-x)$, $Ah=-h$, so $\mathbb E\,h(X_t)=e^{-t}\,\mathbb E\,h(X_0)$.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)

## Proof depends on

- [Chapman–Kolmogorov equation for the transition semigroup](../finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition-add.md)

## Expansion

A full proof page must establish:

- Taking expectations in the martingale identity (polynomials are bounded on compact $E$) and Fubini give the integral equation; $m$ is then continuous, and uniqueness for the linear equation gives $m(t)=e^{tC}m(0)$.
- The degree-one case and the Wright–Fisher heterozygosity example.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658> (moment duality).
