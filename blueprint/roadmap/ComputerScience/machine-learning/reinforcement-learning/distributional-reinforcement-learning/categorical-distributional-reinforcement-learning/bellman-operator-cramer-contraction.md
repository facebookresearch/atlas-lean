# The distributional Bellman operator is a √γ-contraction in the supremum Cramér metric

The distributional Bellman operator shrinks the supremum Cramér metric by the factor $\sqrt{\gamma}$, for every reward–transition kernel and with no moment conditions. Then $\mathcal{T}^\pi$ is a $\sqrt{\gamma}$-contraction for $\bar \ell_2$.

Let $\mathsf{p}$ be a reward–transition kernel, $\gamma \in [0,1)$ and $\pi$ a stochastic policy, with [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) $\mathcal{T}^\pi$ and [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md) $\bar \ell_2$. Then for all $\eta, \mu \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$,

$$\bar \ell_2(\mathcal{T}^\pi \eta, \mathcal{T}^\pi \mu) \le \sqrt{\gamma} \, \bar \ell_2(\eta, \mu)$$

in $[0, \infty]$, with $0 \cdot \infty = 0$.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Proof depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

For $\gamma > 0$ and probability measures $\nu_1, \nu_2$, the substitution $t' = (t - r)/\gamma$ gives

$$\ell_2^2\bigl((f_{r,\gamma})_\# \nu_1, (f_{r,\gamma})_\# \nu_2\bigr) = \int \Bigl(F_{\nu_1}\bigl(\tfrac{t - r}{\gamma}\bigr) - F_{\nu_2}\bigl(\tfrac{t - r}{\gamma}\bigr)\Bigr)^2 dt = \gamma \, \ell_2^2(\nu_1, \nu_2).$$

The distribution function of $(\mathcal{T}^\pi \eta)^{(x,a)}$ at $t$ is $\sum_{x',a'} \pi(a' \mid x') \int F_{\eta^{(x',a')}}((t - r)/\gamma) \, \mathsf{p}(dr, x' \mid x,a)$, an average with total weight $1$. By Jensen's inequality the squared difference at $t$ is at most the average of the squared differences, and Tonelli's theorem in $t$ gives

$$\ell_2^2\bigl((\mathcal{T}^\pi \eta)^{(x,a)}, (\mathcal{T}^\pi \mu)^{(x,a)}\bigr) \le \sum_{(x',a')} \pi(a' \mid x') \int \gamma \, \ell_2^2\bigl(\eta^{(x',a')}, \mu^{(x',a')}\bigr) \, \mathsf{p}(dr, x' \mid x,a) \le \gamma \, \bar \ell_2^2(\eta, \mu).$$

The integrands $r \mapsto F_\nu((t - r)/\gamma)$ are monotone, hence measurable. For $\gamma = 0$ both images are the reward marginal, so the left side is $0$. The joint kernel enters only as the mixing measure, so no independence of reward and next state is used.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.2, first part of the proof of Proposition 2 in appendix Section 9 (the operator $\mathcal{T}^\pi$ is a $\sqrt{\gamma}$-contraction in $\bar \ell_2$).
