# Spectral threshold for mutation–selection equilibrium on an infinite trait lattice

**Model.** Individuals carry a trait $i \in \mathbb{Z}$ with mortality rate $\mu_i > 0$. In a population with carrying capacity $N$, births occur at per-capita rate $\lambda(1 - n/N)$ (logistic regulation on the total size $n$), and a newborn of a parent with trait $k$ has trait $i$ with probability $p_{i-k}$ (mutation kernel $\mathbf p$ on $\mathbb{Z}$). As $N \to \infty$ the trait densities $x_i(t) = \lim n_i(t)/N$ solve
$$\dot x_i = \lambda\Big(1 - \sum_j x_j\Big)(P\mathbf{x})_i - \mu_i x_i, \qquad (P\mathbf{x})_i = \sum_k x_k p_{i-k},\quad i \in \mathbb{Z},$$
and the total mass $m = \sum_i x_i$ satisfies $\dot m = \lambda m(1-m) - \sum_i \mu_i x_i$. For $\mathbf{x} \ne 0$, the trait frequencies $\pi_i = x_i/m$ satisfy
$$\dot\pi_i = \lambda(1-m)\Big(\sum_k \pi_k p_{i-k} - \pi_i\Big) + \pi_i\big(\bar\mu - \mu_i\big), \qquad \bar\mu = \sum_i \mu_i\pi_i .$$
Let $D = \operatorname{diag}(\mu_i)$ and $L = D^{-1}P$, with spectral radius $r(L)$.

**Theorem.**
1. *(Well-posedness and law of large numbers.)* The system has a unique maximal mild solution in the appropriate weighted $\ell^1$ space, global and invariant on the natural cone. If $\mu_i \le C(1+|i|)^q$ and $\mathbf p$ and the initial data have finite $(1+|i|)^{11q}$ moments, then for each $t$ and $K_1$ there are $K_2, K_3$ such that $\|\mathbf{X}(0) - \mathbf{x}_0\|_1 \le K_1\sqrt{\log N/N}$ implies
$$\mathbb{P}\Big(\sup_{0 \le s \le t}\|\mathbf{X}(s) - \mathbf{x}(s)\|_1 > K_2\sqrt{\tfrac{\log N}{N}}\Big) \le K_3\frac{\log N}{N}, \qquad \mathbf{X} = N^{-1}\mathbf{n}.$$
2. *(Confinement and Perron–Frobenius.)* If $\inf_i \mu_i > 0$, $\mu_i \to \infty$ as $|i| \to \infty$, and $\mathbf p$ is irreducible, then $L$ is compact, $r(L) > 0$ is an algebraically simple eigenvalue with a strictly positive eigenvector, and no other real eigenvalue has a nonnegative eigenvector.
3. *(Threshold.)* Under the same hypotheses, if $\lambda r(L) \le 1$ there is no nonzero equilibrium; if $\lambda r(L) > 1$ there is a unique nonzero equilibrium, strictly positive, with total mass $m^* = 1 - 1/(\lambda r(L))$ and trait profile proportional to the Perron eigenvector of $L$. Truncations $L_I$ to $|i| \le I$ satisfy $\|L_I - L\| \to 0$ and $r(L_I) \to r(L)$.
4. *(No mutation.)* If $p_0 = 1$, $\mu^* = \min\{\mu_i : x_i(0) > 0\}$ is attained on the class $J^*$ and $\lambda > \mu^*$, then $x_i(t) \to (1 - \mu^*/\lambda)\,x_i(0)/\sum_{j \in J^*}x_j(0)$ for $i \in J^*$ and $x_i(t) \to 0$ otherwise; if the infimum is not attained, $m(t) \to 1 - \mu^*/\lambda$ while every $x_i(t) \to 0$ (the population drifts toward ever-fitter traits without settling).

## Depends on

## Expansion

At equilibrium $\lambda(1 - m)P\mathbf{x} = D\mathbf{x}$, i.e. $L\mathbf{x} = \mathbf{x}/(\lambda(1-m))$, so a nonnegative equilibrium is a nonnegative eigenvector of $L$ with eigenvalue in $(1/\lambda, \infty)$. Growth of $\mu_i$ at infinity makes $D^{-1}$ compact and hence $L$ compact; irreducibility of the mutation kernel makes $L$ irreducible on the positive cone, and the Krein–Rutman theorem (in the strongly positive form of Theorem 2) gives the Perron eigenpair, which forces the unique equilibrium. Without confinement ($\mu_i$ bounded) mass can escape to infinity in trait space, as the no-mutation case already shows.

## Sources

- P. Pollett, "Mutation–selection balance on an infinite trait space: confinement, drift and equilibrium", arXiv:2609.02086 (2026), Theorems 1–7 and Propositions 1–3, <https://doi.org/10.48550/arXiv.2609.02086>.
