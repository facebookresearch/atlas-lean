# Ξ-coalescent limits of asymmetric Wright–Fisher populations

**Model.** In an asymmetric Wright–Fisher (AWF) population of fixed size $N$, in each generation an independent copy of a random probability vector $\boldsymbol\eta^{(N)} = (\eta^{(N)}_1,\dots,\eta^{(N)}_N)$ is drawn, and each child independently picks parent $i$ with probability $\eta^{(N)}_i$, so offspring numbers are multinomial$(N, \boldsymbol\eta^{(N)})$. The weights need not be exchangeable (reproductive success can depend on the label), but they are redrawn independently each generation (non-heritable success). Let

$$c_N = \mathbb E\Big[\sum_{i=1}^N \big(\eta^{(N)}_i\big)^2\Big]$$

be the probability that two sampled genes share a parent one generation back, and let $(\tilde\eta_1, \tilde\eta_2, \dots)$ be a size-biased reordering of $\boldsymbol\eta^{(N)}$.

**Theorem.** Let $\Pi^{(N,n)}$ be the ancestral partition of a sample of $n$ genes.
1. *(Criterion.)* For every $n$, the one-step transition matrix $P^{(N,n)}$ of $\Pi^{(N,n)}$ satisfies $P^{(N,n)} = \mathrm{Id} + c_N Q^{(n)}_\Xi + o(c_N)$, with $Q^{(n)}_\Xi$ the rate matrix of a $\Xi$-coalescent on partitions of $\{1,\dots,n\}$, and $c_N \to 0$, if and only if for all $j \ge 1$ and $b_1 \ge \dots \ge b_j \ge 2$ the limits

$$\phi_j(b_1,\dots,b_j) = \lim_{N\to\infty}\frac{1}{c_N}\,\mathbb E\Big[\prod_{i=1}^j \tilde\eta_i^{\,b_i - 1}\prod_{i=1}^{j-1}\Big(1 - \sum_{k=1}^i \tilde\eta_k\Big)\Big]$$

exist; the $\phi_j$ are then the $\Xi$-coalescent's simultaneous-merger rates. In that case $(\Pi^{(N,n)}_{\lfloor t/c_N\rfloor})_{t\ge0}$ converges, for every $n$, in the Skorokhod space to this $\Xi$-coalescent.
2. *(Kingman case.)* If $\mathbb E\big[(\eta_2^{(N)})^3 + \dots + (\eta_N^{(N)})^3\big] = o(c_N)$, $\mathbb E\big[(\eta_1^{(N)})^\beta\big] = o(c_N)$ for some $\beta > 2$, and $c_N \to 0$, the limit is Kingman's coalescent.
3. If instead the expansion of item 1 holds with $c_N \to c > 0$, the genealogy converges (without time rescaling) to a discrete-time Markov chain with transition matrix $\mathrm{Id} + c\,Q^{(n)}_\Xi$.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)
- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)

## Expansion

Ancestral lineages choose parents by sampling with replacement from the paintbox $\boldsymbol\eta^{(N)}$, so the one-step merger probabilities are paintbox moments; size-biased ordering turns them into the displayed product formula, the analogue of the Möhle–Sagitov criterion for exchangeable Cannings models. Because weights are redrawn every generation, the ancestral process is still Markov, which is all the convergence argument needs; exchangeability is not. The framework covers highly asymmetric offspring laws (one dominant parent), random recurrent bottlenecks, and exponential fitness models, and transfers to sampling without replacement (the analogue of Cannings models) with the same limits.

## Sources

- Arno Siri-Jégousse and Alejandro H. Wences, "Exchangeable coalescents beyond the Cannings class", J. Math. Biol. 90 (2025), 7, <https://doi.org/10.1007/s00285-024-02173-x>. Numbering follows the arXiv version, arXiv:2212.02154 (2022): Theorems 2.1, 2.2 and Proposition 3.2, <https://doi.org/10.48550/arXiv.2212.02154>.
