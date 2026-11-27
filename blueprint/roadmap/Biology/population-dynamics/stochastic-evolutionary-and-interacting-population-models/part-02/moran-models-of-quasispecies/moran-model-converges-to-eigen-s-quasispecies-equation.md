# Moran model converges to Eigen's quasispecies equation

Let there be $N$ genotypes with fitnesses $f_1,\dots,f_N \ge 0$ and a stochastic mutation matrix $(Q_{ij})$, where $Q_{ij}$ is the probability that an offspring of genotype $i$ has genotype $j$. **Eigen's quasispecies model** is the system of ordinary differential equations on the simplex $\{x \in \mathbb R^N : x_i \ge 0,\ x_1+\dots+x_N = 1\}$

$$x_i'(t) = \sum_{k=1}^{N} f_k Q_{ki}\, x_k(t) - x_i(t) \sum_{k=1}^{N} f_k x_k(t), \qquad 1 \le i \le N.$$

The **Moran model** with population size $m$ is the Markov chain $(Z_n)_{n\ge 0}$ on $\{z \in \mathbb N^N : z_1+\dots+z_N = m\}$ whose only moves are $z \to z - e_i + e_j$, with probabilities, for $i \neq j$,

$$p(z, z - e_i + e_j) = \frac{z_i}{m} \cdot \frac{1}{\lambda m} \sum_{k=1}^{N} f_k Q_{kj}\, z_k,$$

where $\lambda \ge \max_i f_i$ is a constant: a parent is chosen in proportion to fitness, its offspring is mutated by $Q$ and replaces a uniformly chosen individual.

**Theorem (Dalmau, Theorem 3.1).** Suppose $Z_0/m \to x^0$ as $m \to \infty$ and let $x(t)$ solve Eigen's system with $x(0) = x^0$. Then for every $\delta > 0$ and $T > 0$,

$$\lim_{m\to\infty} P\Big( \sup_{0 \le t \le T} \Big| \frac{1}{m} Z_{\lfloor \lambda m t \rfloor} - x(t) \Big| > \delta \Big) = 0.$$

So Eigen's deterministic quasispecies dynamics is the infinite-population limit of the Moran model in which mutations arise as replication errors, with time measured in units of $\lambda m$ Moran steps.

## Depends on

- [Interior equilibrium of the master-sequence frequency](../../../eigen-s-quasispecies-error-threshold/master-equilibrium.md)

## Expansion

The proof applies Kurtz's theorem on the convergence of density-dependent families of Markov chains (stated as Theorem 4.1 of the paper). The rescaled chain $X^m_n = Z_n/m$ has jumps of size $1/m$; its expected increment per step, multiplied by the time scale $\alpha_m = \lambda m$, converges uniformly to the Eigen vector field

$$F_j(x) = \sum_{k} f_k Q_{kj} x_k - x_j \sum_k f_k x_k,$$

because the probability of gaining a type-$j$ individual is $\frac{1}{\lambda m}\sum_k f_k Q_{kj} z_k$ times the probability $1 - z_j/m$ of replacing a non-$j$ individual, and similarly for losses. The second moments of the increments are $O(1/m^2)$ per step, so over $\lambda m T$ steps the fluctuations vanish, and the Lipschitz continuity of $F$ on the simplex gives uniform convergence on $[0,T]$ in probability.

## Sources

- J. Dalmau, *Convergence of a Moran model to Eigen's quasispecies model*, arXiv:1404.2133 (2014). <https://doi.org/10.48550/arXiv.1404.2133>. Published version: Journal of Theoretical Biology 420 (2017), 36–40, <https://doi.org/10.1016/j.jtbi.2017.02.035>; locators above refer to the arXiv version.
