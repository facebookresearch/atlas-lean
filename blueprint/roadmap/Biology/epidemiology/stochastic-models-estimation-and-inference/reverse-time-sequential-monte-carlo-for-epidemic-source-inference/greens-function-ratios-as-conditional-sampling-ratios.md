# Green's function ratios as conditional sampling ratios

Let $(X_n)$ be a Markov chain with initial law $\mu$ and transition kernel $P$, stopped at the hitting time $\tau_T$ of a target set $T$, and let

$$ G(\mu, A) = \mathbb{E}_\mu\Big[\sum_{i=0}^{\tau_T} \mathbf{1}_A(X_i)\Big] $$

be its Green's function. Nagasawa's formula expresses the time reversal of the stopped chain as

$$ \widetilde P(x_i, x_{i-1}) = \frac{G(\mu, x_{i-1})}{G(\mu, x_i)}\, P(x_{i-1}, x_i) . $$

**Proposition.** Suppose a transition changes only some coordinates, $x_{n-1} = (z, y)$ and $x_n = (z, \bar y)$, and the conditional sampling distribution $\pi(y \mid z) = \mathbb{P}_\mu(Y_n = y \mid Z_n = z)$ does not depend on $n$ for almost every $z$. Then

$$ \frac{G(\mu, (z, y))}{G(\mu, (z, \bar y))} = \frac{\pi(y \mid z)}{\pi(\bar y \mid z)} . $$

Replacing $\pi$ by a tractable approximation $\hat\pi$ gives a reverse-time proposal $\hat P((z,\bar y),(z,y)) \propto \hat\pi(y\mid z)\,P((z,y),(z,\bar y))/\hat\pi(\bar y\mid z)$ for sequential Monte Carlo started at the target, with incremental importance weights equal to the normalizing constant times $\hat\pi(\bar y\mid z)/\hat\pi(y\mid z)$; combined with stopping-time (multilevel) resampling this estimates functionals of trajectories conditioned on ending in a rare set.

## Expansion

Write $G(\mu,(z,y)) = \sum_n \mathbb{E}_\mu[\mathbf{1}_{\{y\}}(Y_n)\mathbf{1}_{\{z\}}(Z_n)\mathbf{1}_{\{n \le \tau_T\}}]$ after killing the chain at $\tau_T$, condition on $Z_n = z$, and pull out $\pi(y\mid z)$, which is the same for every $n$. The remaining factor depends only on $z$ and cancels in the ratio. The design problem therefore drops from approximating a high-dimensional Green's function to specifying low-dimensional conditional distributions of a few coordinates given the rest; reverse-time proposals of this kind were used earlier for population-genetic models.

## Sources

- Jere Koskela, Dario Spanò, Paul A. Jenkins, "Inference and rare event simulation for stopped Markov processes via reverse-time sequential Monte Carlo", Statistics and Computing 28 (2018), 131–144, <https://doi.org/10.1007/s11222-017-9722-1>. Published version of arXiv:1603.02834, cited next; locators there refer to the arXiv version.
- J. Koskela, D. Spanò, P. A. Jenkins, "Inference and rare event simulation for stopped Markov processes via reverse-time sequential Monte Carlo", arXiv:1603.02834 (2016), Section 2 (stopped-chain formulation and SMC), Section 3 (Nagasawa's formula, Proposition 1, Remark 1 and the reverse-time multilevel SMC algorithm). <https://doi.org/10.48550/arXiv.1603.02834>
