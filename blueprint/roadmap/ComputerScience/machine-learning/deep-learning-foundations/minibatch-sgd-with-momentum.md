# Minibatch SGD with momentum

Let $\ell_i(\theta)$ be differentiable losses on $\mathbb R^d$. At step $t\ge1$ choose a nonempty minibatch $B_t$ of sample indices (count repetitions). With $v_0=0$, learning rates $\eta_t>0$ and $0\le\mu<1$, the velocity convention is

$$g_t=|B_t|^{-1}\sum_{i\in B_t}\nabla\ell_i(\theta_{t-1}),\quad v_t=\mu v_{t-1}-\eta_t g_t,\quad \theta_t=\theta_{t-1}+v_t.$$

Setting $\mu=0$ gives minibatch SGD. Using all examples then gives gradient descent on their mean. With a varying learning rate, placing $\eta_t$ inside the velocity as above is not the same as multiplying an accumulated unscaled gradient by the current rate.

## Depends on

- [Empirical risk](../generalization-bounds-and-concentration/empirical-risk.md)

## Background

- [Gradient descent with a step schedule](../../../Analysis/convex-analysis-and-variations/gradient-descent/gradient-descent-trajectory.md)
- [The backward pass is the vector-Jacobian product](../supervised-learning/backpropagation/backward-eq.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 8, §§8.3.1–8.3.2, algorithms 8.1–8.2](https://www.deeplearningbook.org/contents/optimization.html).
