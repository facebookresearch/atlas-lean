# Uniform generator convergence of the Wright–Fisher chain with selection and mutation

Fix $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$, and let $X^{(M)}$ be the Wright–Fisher frequency chain with selection and mutation on $M$ gene copies with $s = \alpha / M$ and $u_i = \theta_i / (2M)$ (for all $M > \max(\lvert\alpha\rvert, \theta_1/2, \theta_2/2)$, so that $0 \le u_i \le 1$ and $s > -1$ and the transition below is well defined): from frequency $x$, mutation gives the [frequency after mutation](mutated-freq.md) $p'$, genic selection gives $p'' = (1 + s) p' / (1 + s p')$, and the next frequency is $k/M$ with $k \sim \mathrm{Bin}(M, p'')$; for $s = 0$ this is the chain whose [drift](integral-binomial-mutated-freq-drift.md) is the mutation drift. Then for every $f \in C^3[0, 1]$,

$$\sup_{x \in [0, 1]} \Bigl\lvert M\bigl(\mathbb{E}_x f(X^{(M)}_1) - f(x)\bigr) - \mathcal{L}_{\alpha, \theta} f(x) \Bigr\rvert \to 0 \qquad (M \to \infty),$$

with $\mathcal{L}_{\alpha, \theta} f = \frac{1}{2} x(1 - x) f'' + \bigl(\alpha x(1 - x) + \frac{1}{2}(\theta_1(1 - x) - \theta_2 x)\bigr) f'$. The convergence is uniform on $[0, 1]$, which is the hypothesis Trotter–Kato-type theorems need; it is not yet convergence of the processes.

## Depends on

- [Allele frequency after one generation of two-way mutation](mutated-freq.md)
- [Drift of the Wright–Fisher chain with mutation](integral-binomial-mutated-freq-drift.md)

## Proof depends on

- [Wright–Fisher diffusion limit, generator form](../diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)

## Expansion

1. A third-order Taylor expansion of $f$ with the first two moments of one generation of the chain and a bound on its third absolute moment, uniformly in $x$.
2. A check: for $\alpha = \theta = 0$ it reduces to [the generator form of the diffusion limit](../diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 6 and Chapter 10, Section 1.
- H. F. Trotter, Approximation of semi-groups of operators, *Pacific J. Math.* 8 (1958), 887–919 (the chain approximation hypothesis).
