# Optional stopping for right-continuous martingales

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $M=(M_t)_{t\ge0}$ a real martingale with right-continuous paths. Let $\sigma\le\tau$ be stopping times with $\tau\le T$ for a constant $T$. Then $M_\sigma$ and $M_\tau$ are integrable and

$$M_\sigma=\mathbb E\bigl[M_\tau\bigm|\mathcal F_\sigma\bigr]\quad\text{almost surely},\qquad\text{so }\ \mathbb E M_\tau=\mathbb E M_\sigma=\mathbb E M_0,$$

where $\mathcal F_\sigma=\{A\in\mathcal F:A\cap\{\sigma\le t\}\in\mathcal F_t\text{ for all }t\ge0\}$. No continuity of the paths and no condition on the filtration is needed.

## Depends on

- [Filtrations and stopping times](filtrations-and-stopping-times.md)

## Proof depends on

- [Optional stopping for martingales at two bounded stopping times](../optional-stopping-theorem/expected-stopped-value-eq.md)

## Expansion

A proof page must approximate $\sigma$ and $\tau$ from above by the stopping times $\sigma_k=\lceil2^k\sigma\rceil/2^k$ and $\tau_k=\lceil2^k\tau\rceil/2^k$, which take finitely many values in $[0,T+1]$; apply discrete optional stopping to the martingale sampled on the dyadic grid of level $k$; use that the variables $M_{\tau_k}=\mathbb E[M_{T+1}\mid\mathcal F_{\tau_k}]$ are uniformly integrable and converge to $M_\tau$ by right-continuity, and similarly for $\sigma_k$; and pass to the limit in $\mathbb E[M_{\tau_k}\mathbf 1_A]=\mathbb E[M_{\sigma_k}\mathbf 1_A]$ for $A\in\mathcal F_\sigma\subseteq\mathcal F_{\sigma_k}$. It should also establish the measurability of $M_\sigma$ with respect to $\mathcal F_\sigma$, which uses right-continuity (progressive measurability).

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 3.
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Chapter 1, Section 3.
