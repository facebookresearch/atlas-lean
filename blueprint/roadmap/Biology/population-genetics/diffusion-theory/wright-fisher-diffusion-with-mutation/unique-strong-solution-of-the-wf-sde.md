# Unique strong solution of the Wright–Fisher stochastic differential equation

For $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$, the equation

$$dX_t = \Bigl(\alpha X_t (1 - X_t) + \frac{1}{2}\bigl(\theta_1 (1 - X_t) - \theta_2 X_t\bigr)\Bigr) dt + \sqrt{X_t (1 - X_t)}\, dW_t$$

has a unique strong solution from every starting point in $[0, 1]$, and its law is the unique law of the martingale problem for $\mathcal{L}_{\alpha, \theta}$.

By the [Yamada–Watanabe theorem](../../../../Probability/stochastic-calculus/stochastic-differential-equations/yamada-watanabe-theorem-weak-existence-pathwise.md) this follows from weak existence, since the solution of the martingale problem from [the exponential tilt](existence-of-the-selection-mutation-wf-diffusion.md) is a [weak solution of the equation](wf-martingale-problem-solutions-are-weak-sde-sol.md), and from [pathwise uniqueness](../wright-fisher-diffusion-with-selection-and-mutat/pathwise-uniqueness-for-the-wf-sde.md). The law is identified by [the uniqueness under the inverse tilt](uniqueness-for-the-selection-mutation-martingale.md), and in the neutral case without mutation by [the neutral uniqueness in law](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-neutral-martingale-pro.md).

## Depends on

- [Yamada–Watanabe theorem: weak existence and pathwise uniqueness give a strong solution and uniqueness in law](../../../../Probability/stochastic-calculus/stochastic-differential-equations/yamada-watanabe-theorem-weak-existence-pathwise.md)
- [Wright–Fisher martingale-problem solutions are weak solutions of the equation](wf-martingale-problem-solutions-are-weak-sde-sol.md)
- [Pathwise uniqueness for the Wright–Fisher equation](../wright-fisher-diffusion-with-selection-and-mutat/pathwise-uniqueness-for-the-wf-sde.md)
- [Existence of the Wright–Fisher diffusion with selection and mutation by an exponential tilt](existence-of-the-selection-mutation-wf-diffusion.md)
- [Uniqueness for the selection–mutation martingale problem by an inverse tilt](uniqueness-for-the-selection-mutation-martingale.md)
- [Uniqueness in law for the neutral Wright–Fisher martingale problem](../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-neutral-martingale-pro.md)

## Expansion

The statement assembles the results it cites; a full proof page checks that their hypotheses match for all $\alpha \in \mathbb{R}$ and $\theta_i \ge 0$.

## Sources

- T. Yamada and S. Watanabe, On the uniqueness of solutions of stochastic differential equations, *J. Math. Kyoto Univ.* 11 (1971), 155–167, <https://doi.org/10.1215/kjm/1250523691> (the Yamada–Watanabe principle).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer (1991), <https://doi.org/10.1007/978-1-4612-0949-2>, Chapter 5.
