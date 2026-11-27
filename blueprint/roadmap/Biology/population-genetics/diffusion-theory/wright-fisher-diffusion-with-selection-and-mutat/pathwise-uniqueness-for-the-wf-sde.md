# Pathwise uniqueness for the Wright–Fisher stochastic differential equation

For $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$, pathwise uniqueness holds for $[0, 1]$-valued solutions, on a common filtered space with a common Brownian motion, of

$$dX_t = b(X_t)\, dt + \sigma(X_t)\, dW_t, \qquad b(x) = \alpha x (1 - x) + \tfrac{1}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr), \quad \sigma(x) = \sqrt{x (1 - x)}.$$

This is a special case of [Yamada–Watanabe pathwise uniqueness](../../../../Probability/stochastic-calculus/stochastic-differential-equations/yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md) with modulus $h(u) = \sqrt{u}$, which satisfies the Osgood condition $\int_{0^+} h(u)^{-2}\, du = \int_{0^+} u^{-1}\, du = \infty$. Extend $\sigma$ by $0$ outside $[0, 1]$; it is then [$1/2$-Hölder](abs-sqrt-mul-one-sub-sub-le.md) on $\mathbb{R}$. Extend $b$ by its value at the nearest point of $[0, 1]$; it is then globally Lipschitz. The extensions do not affect $[0, 1]$-valued solutions.

## Depends on

- [Yamada–Watanabe pathwise uniqueness (Hölder-1/2 diffusion coefficient)](../../../../Probability/stochastic-calculus/stochastic-differential-equations/yamada-watanabe-pathwise-uniqueness-holder-1-2-d.md)
- [The coefficient √(x(1 − x)) is 1/2-Hölder on the unit interval](abs-sqrt-mul-one-sub-sub-le.md)

## Expansion

1. The extended $\sigma$ satisfies $\lvert \sigma(x) - \sigma(y) \rvert \le \sqrt{\lvert x - y \rvert}$ on $\mathbb{R}$.
2. The extended $b$ is Lipschitz on $\mathbb{R}$.

## Sources

- T. Yamada and S. Watanabe, On the uniqueness of solutions of stochastic differential equations, *J. Math. Kyoto Univ.* 11 (1971), 155–167, <https://doi.org/10.1215/kjm/1250523691> (pathwise uniqueness).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer (1991), <https://doi.org/10.1007/978-1-4612-0949-2>, Chapter 5, Section 2.
