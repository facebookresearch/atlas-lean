# Bellman equation for the return variance

The variance of the discounted return of a fixed policy satisfies a Bellman equation in which the one-step variance of the next-state value, scaled by $\gamma^2$, plays the role of the reward and $\gamma^2$ plays the role of the discount.

Let $M$ be a discounted MDP with finite state and action sets, deterministic rewards $r(z) \in [0, 1]$ for state-action pairs $z = (x, a)$, transition kernel $P$ and discount $\gamma \in [0, 1)$, and let $\pi$ be a deterministic stationary policy. Let $Z_0 = z, Z_1, Z_2, \dots$ be the state-action process that starts at $z$, then draws $X_{t+1} \sim P(\cdot \mid Z_t)$ and sets $Z_{t+1} = (X_{t+1}, \pi(X_{t+1}))$. Define the return variance

$$\Sigma^\pi(z) = \mathbb E\Big[\Big(\sum_{t \ge 0}\gamma^t r(Z_t) - Q^\pi(z)\Big)^2 \,\Big|\, Z_0 = z\Big],$$

the discounted one-step variance $\sigma_{V^\pi}(z) = \gamma^2\,\mathrm{Var}_{Y \sim P(\cdot \mid z)}(V^\pi(Y))$, and $(P^\pi f)(z) = \sum_y P(y \mid z) f(y, \pi(y))$ for $f : S \times A \to \mathbb R$.

**Lemma.** For every deterministic stationary policy $\pi$,

$$\Sigma^\pi = \sigma_{V^\pi} + \gamma^2 P^\pi \Sigma^\pi,$$

so that $\Sigma^\pi = (I - \gamma^2 P^\pi)^{-1}\sigma_{V^\pi}$.

## Depends on

- [Bellman values are expected discounted returns](../bellman-values-are-expected-discounted-returns.md)
- [Q-value of an action](../../../heuristic-search-and-planning/value-iteration/q-value.md)
- [Empirical MDP from a generative model](empirical-mdp-from-a-generative-model.md)

## Proof depends on

None.

## Expansion

Write the centered return as $(\sum_{t \ge 1}\gamma^t r(Z_t) - \gamma Q^\pi(Z_1)) - (Q^\pi(z) - r(z) - \gamma Q^\pi(Z_1))$. Conditionally on $Z_1$ the first bracket has mean zero, because $Q^\pi(Z_1)$ is the expected discounted return from $Z_1$, so the cross term vanishes. The square of the first bracket has conditional expectation $\gamma^2\Sigma^\pi(Z_1)$, and since $Q^\pi(z) = r(z) + \gamma\,\mathbb E[Q^\pi(Z_1)]$ the second bracket is $\gamma(\mathbb E[Q^\pi(Z_1)] - Q^\pi(Z_1))$ with $Q^\pi(Z_1) = V^\pi(X_1)$, whose variance is $\sigma_{V^\pi}(z)$. Averaging over $Z_1 \sim P^\pi(\cdot \mid z)$ gives the equation, and $I - \gamma^2P^\pi$ is invertible because $\gamma^2 < 1$. This is the law of total variance for the discounted return; Sobel (1982) and Munos and Moore (1999) give the state-value form. It is the starting point of the total-variance technique used by the minimax generative-model bounds.

## Sources

- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: definitions of $\Sigma^\pi$ and $\sigma_{V^\pi}$ (Section 4.1, p. 332), Lemma 7 and its proof (pp. 336–337), first equality of Lemma 8, equation (18) (p. 337).
- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): equation (2) (Section 4), the same identity in the notation $\Sigma^\pi_M = \gamma^2\mathrm{Var}_P(V^\pi_M) + \gamma^2P^\pi\Sigma^\pi_M$.
