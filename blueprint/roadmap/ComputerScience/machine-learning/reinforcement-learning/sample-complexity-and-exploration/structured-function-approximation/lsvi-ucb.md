# LSVI-UCB

LSVI-UCB (least-squares value iteration with upper confidence bounds) is the episodic algorithm that, before each episode, fits linear predictors backwards in $h$ by ridge regression on all past transitions, adds an elliptical bonus and caps the result at $H$ to obtain optimistic action values (which need not be linear in the features), then acts greedily.

**Input.** An episodic MDP with horizon $H$, finite action set $\mathcal{A}$, a known feature map $\phi : \mathcal{S} \times \mathcal{A} \to \mathbb{R}^d$, a regularization parameter $\lambda > 0$, a bonus multiplier $\beta \ge 0$ (or a sequence $\beta_k$), and $K$ episodes; the initial state $x^k_1$ of episode $k$ may be chosen by an adversary. Write $\phi^\tau_h = \phi(x^\tau_h, a^\tau_h)$ for the feature observed at step $h$ of episode $\tau$.

**Procedure.** For each episode $k = 1, \dots, K$:

1. Receive $x^k_1$. Set $Q^k_{H+1} \equiv 0$. For $h = H, H-1, \dots, 1$ compute

$$
\Lambda^k_h = \lambda I + \sum_{\tau=1}^{k-1} \phi^\tau_h (\phi^\tau_h)^{\mathsf T}, \qquad w^k_h = (\Lambda^k_h)^{-1} \sum_{\tau=1}^{k-1} \phi^\tau_h \Big[ r_h(x^\tau_h, a^\tau_h) + \max_{a \in \mathcal{A}} Q^k_{h+1}(x^\tau_{h+1}, a) \Big],
$$

$$
Q^k_h(\cdot,\cdot) = \min\Big\{ (w^k_h)^{\mathsf T} \phi(\cdot,\cdot) + \beta \big[\phi(\cdot,\cdot)^{\mathsf T} (\Lambda^k_h)^{-1} \phi(\cdot,\cdot)\big]^{1/2},\ H \Big\}.
$$

2. For $h = 1, \dots, H$ take $a^k_h \in \arg\max_{a} Q^k_h(x^k_h, a)$ and observe $x^k_{h+1}$ (and the reward).

The source's Algorithm 1 receives $x^k_1$ before the backward sweep, which does not use it.

For $k = 1$ the sums are empty, so $\Lambda^1_h = \lambda I$ and $w^1_h = 0$. The vector $w^k_h$ is the ridge estimate for the rows $(\phi^\tau_h)^{\mathsf T}$, $\tau < k$, with the bracketed responses, that is, the minimizer of the ridge objective $\sum_{\tau < k} \big(r_h(x^\tau_h,a^\tau_h) + \max_a Q^k_{h+1}(x^\tau_{h+1},a) - w^{\mathsf T}\phi^\tau_h\big)^2 + \lambda \lVert w \rVert_2^2$. The function $Q^k_h$ is represented by $(w^k_h, \Lambda^k_h)$ and only evaluated where needed.

**Cost.** The algorithm stores $\Lambda_h$, $w_h$, the observed rewards and the features $\{\phi(x^k_h, a)\}_{a \in \mathcal{A}}$, which is $O(d^2 H + dAT)$ space with $T = KH$ and $A = |\mathcal{A}|$. With Sherman–Morrison updates of $(\Lambda^k_h)^{-1}$, the source's count is $O(d^2 A K)$ time per step, dominated by the maxima over $a$ in the regression targets, so $O(d^2 A K T)$ in total. The running time does not depend on $|\mathcal{S}|$.

## Depends on

- [Ridge estimate](../../../supervised-learning/least-squares-ridge-and-lasso-regression/ridge-estimate.md)
- [Ridge objective](../../../supervised-learning/least-squares-ridge-and-lasso-regression/ridge.md)

## Proof depends on

None.

## Expansion

The procedure is least-squares value iteration (replace the unknown Bellman backup by ridge regression on sampled next states) with a linear-bandit style bonus $\beta \lVert \phi \rVert_{(\Lambda^k_h)^{-1}}$; truncation at $H$ keeps the estimates at most $H$ (it does not make them nonnegative). The guarantee of the algorithm is on the [regret page](regret-of-lsvi-ucb-in-linear-mdps.md); there the source sets $\lambda = 1$ and $\beta = c\,dH\sqrt{\log(2dT/p)}$.

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Algorithm 1 and the discussion after Theorem 3.1 (space and running time). <https://arxiv.org/abs/1907.05388v2>
