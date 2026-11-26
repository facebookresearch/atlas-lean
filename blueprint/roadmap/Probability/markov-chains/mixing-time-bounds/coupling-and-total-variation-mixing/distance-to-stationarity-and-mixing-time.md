# Distance to stationarity and total-variation mixing time

Let $P$ be a Markov transition kernel on a finite state space $S$ and $\pi$ a probability distribution on $S$. Write $\|\mu - \nu\|_{TV} = \max_{A \subseteq S} |\mu(A) - \nu(A)|$. For $t \in \mathbb{N}$ define

$$
d(t) = \max_{x \in S} \|P^t(x,\cdot) - \pi\|_{TV}, \qquad \bar d(t) = \max_{x,y \in S} \|P^t(x,\cdot) - P^t(y,\cdot)\|_{TV},
$$

and for $\varepsilon > 0$ the *mixing time* $t_{\mathrm{mix}}(\varepsilon) = \min\{t : d(t) \le \varepsilon\} \in \mathbb{N} \cup \{\infty\}$, with value $\infty$ when no such $t$ exists (no irreducibility or aperiodicity is assumed).

## Depends on

- [Stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
- [Stationary distribution](../../kolmogorov-s-criterion-for-reversibility/is-stationary.md)
- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
