# Parameter-free Le Cam-Birgé tournament: agnostic hypothesis selection in Hellinger distance

Let $q_1, \dots, q_M$ be distributions on a finite set and let the sample be $n$ i.i.d. draws from an arbitrary $p$. Run the Le Cam-Birgé test on every pair of candidates, assign to each candidate its *maximum defeat radius* (the largest Hellinger separation at which it loses a pairwise comparison, a quantity computed from the test outcomes and the pairwise distances alone), and let $\hat q$ minimize it. The selector needs no knowledge of the approximation error. If some candidate $q_{i_0}$ satisfies $h(p, q_{i_0}) \le r$, then

$$
\Pr\bigl[h(p, \hat q) > 11 r\bigr] \le 2(M-1)\,e^{-4 n r^2}.
$$

Consequently, for any class $\mathcal{P}$ of distributions with a finite Hellinger $r$-cover of size $M$, running the tournament on the cover returns, for every $p \in \mathcal{P}$, a hypothesis within Hellinger distance $11r$ of $p$ with the same failure probability.

## Proof sketch

By the radius form of the Le Cam-Birgé test and a union bound over the $M-1$ comparisons involving $q_{i_0}$ (two error directions each), with the stated probability $q_{i_0}$ wins every comparison against candidates far from it. On that event the defeat radius of $q_{i_0}$ is $O(r)$, so the minimizer $\hat q$ has defeat radius $O(r)$ too, which forces $\hat q$ to be close to $q_{i_0}$; the explicit constants combine to $h(p,\hat q) \le 11r$ by the triangle inequality.

## Depends on

- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)
- [Robust Le Cam-Birgé test with clipped likelihood-ratio weights](le-cam-birge-pairwise-test.md)

## Sources

- Lucien Le Cam, "Convergence of Estimates Under Dimensionality Restrictions", The Annals of Statistics 1(1), 1973.
- Lucien Birgé, "Approximation dans les espaces métriques et théorie de l'estimation", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete 65, 1983.
