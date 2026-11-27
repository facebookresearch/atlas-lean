# Total-variance bound

For any policy, summing the square roots of one-step value variances along the discounted occupancy costs only $\sqrt{2/(1-\gamma)^3}$ rather than the naive $1/(1-\gamma)^2$. This is the factor-$\sqrt{1/(1-\gamma)}$ saving behind minimax generative-model sample bounds.

Let $M$ be a discounted MDP with finite state and action sets, rewards in $[0, 1]$, transition kernel $P$ and discount $\gamma \in (0, 1)$, and use the matrix notation of the empirical-MDP page: $P^\pi$ is the state-action transition matrix of a deterministic stationary policy $\pi$, $\mathrm{Var}_P(V)$ the vector of one-step variances, and the square root acts entrywise.

**Lemma.** For every deterministic stationary policy $\pi$, the return variance satisfies $\|\Sigma^\pi\|_\infty \le \gamma^2/(1-\gamma)^2$, where $\Sigma^\pi$ is the return variance of the Bellman-equation page, and

$$\Big\|(I - \gamma P^\pi)^{-1}\sqrt{\mathrm{Var}_P(V^\pi)}\Big\|_\infty \le \sqrt{\frac{2}{(1-\gamma)^3}}.$$

In the scaling with $\sigma_{V^\pi} = \gamma^2\mathrm{Var}_P(V^\pi)$ and $\beta = 1/(1-\gamma)$, the earlier form of the bound reads $\|\Sigma^\pi\|_\infty \le \beta^2$ and $\|(I - \gamma P^\pi)^{-1}\sqrt{\sigma_{V^\pi}}\|_\infty \le 2\log(2)\,\beta^{3/2}$.

## Depends on

- [Empirical MDP from a generative model](empirical-mdp-from-a-generative-model.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)
- [Bellman equation for the return variance](bellman-equation-for-the-return-variance.md)

## Proof depends on

- [Finite Jensen inequality for concave functions](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/finite-jensen-inequality-for-concave-functions.md)

## Expansion

The rows of $(1-\gamma)(I - \gamma P^\pi)^{-1}$ are probability distributions, so Jensen's inequality gives, for a nonnegative vector $v$,

$$\|(I - \gamma P^\pi)^{-1}\sqrt v\|_\infty \le \sqrt{\frac{1}{1-\gamma}\|(I - \gamma P^\pi)^{-1}v\|_\infty} \le \sqrt{\frac{2}{1-\gamma}\|(I - \gamma^2P^\pi)^{-1}v\|_\infty},$$

where the last step writes $(I - \gamma P^\pi)^{-1} = ((1-\gamma)(I - \gamma P^\pi)^{-1} + \gamma I)(I - \gamma^2P^\pi)^{-1}$. With $v = \mathrm{Var}_P(V^\pi)$ the Bellman equation for the return variance gives $\gamma^2(I - \gamma^2P^\pi)^{-1}v = \Sigma^\pi$, and $\|\Sigma^\pi\|_\infty \le \gamma^2/(1-\gamma)^2$, so the right side is $\sqrt{2/(1-\gamma)^3}$. The earlier argument instead splits the series of $(\gamma P^\pi)^k$ into blocks of length $t$, applies Cauchy–Schwarz within blocks and optimizes over $t$, which gives the constant $2\log 2$. Without the variance structure, $\sqrt{\mathrm{Var}_P(V^\pi)} \le 1/(1-\gamma)$ entrywise only gives $1/(1-\gamma)^2$.

## Sources

- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Lemma 2 and Lemma 5 (Sections 4 and 4.1), with the proof of Lemma 5 in the appendix.
- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: Lemma 8, equations (18)–(21) (pp. 337–338).
