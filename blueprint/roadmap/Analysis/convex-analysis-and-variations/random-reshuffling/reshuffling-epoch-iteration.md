# Random reshuffling epoch iteration

Let $n\ge 1$ be an integer and let $f_k\colon\mathbb R^d\to\mathbb R$ be
differentiable for each label $k\in I=\{1,\ldots,n\}$. The finite-sum
objective is the average

$$
f(x)=\frac{1}{n}\sum_{k=1}^n f_k(x).
$$

Fix a step size $\gamma>0$ and an initial point $x_0\in\mathbb R^d$. For an
epoch $t$, an order $\pi_t$ is a bijection from the positions
$\{0,\ldots,n-1\}$ to $I$, so $\pi_t(i)$ is the label used at position $i$.
Given the epoch start $x_t$ and this order, define $x_t^i$ for $0\le i\le n$
and the next epoch start by

$$
x_t^0=x_t,\qquad
x_t^{i+1}=x_t^i-\gamma\nabla f_{\pi_t(i)}(x_t^i)
\quad(0\le i\lt n),\qquad
x_{t+1}=x_t^n.
$$

The recurrence is deterministic once the order is given. A random
reshuffling run of $T$ epochs, for a nonnegative integer $T$, draws a fresh
[uniformly random rearrangement](../../../ComputerScience/randomized-algorithms/average-case-running-time/uniform-permutation.md)
of the list $(1,\ldots,n)$ at the start of each epoch $0\le t\lt T$.
For every bijection $\sigma$ and every previous permutation history of
positive probability, the conditional probability
that $\pi_t=\sigma$ is $1/n!$ (with no history at $t=0$). Thus the labels
are used without replacement within an epoch, but an order may recur in
another epoch. When $n=1$, the only order has $\pi_t(0)=1$ and the epoch
consists of one step, $x_{t+1}=x_t-\gamma\nabla f_1(x_t)$.

## Depends on

- [Gradient of a function on Euclidean coordinate space](../../../Probability/stochastic-calculus/fokker-planck-equation/grad.md) for the component gradients.
- [Uniformly random rearrangement of a list](../../../ComputerScience/randomized-algorithms/average-case-running-time/uniform-permutation.md) for the per-epoch sampling law, not the recurrence at a prescribed order.

## Sources

- Konstantin Mishchenko, Ahmed Khaled and Peter Richtárik,
  [*Random Reshuffling: Simple Analysis with Vast Improvements*](https://arxiv.org/pdf/2006.05988v3#page=2),
  arXiv:2006.05988v3, equation (1) for the objective, and §1.1, p. 2,
  Algorithm 1 for the iteration and the fresh draw at each epoch.
