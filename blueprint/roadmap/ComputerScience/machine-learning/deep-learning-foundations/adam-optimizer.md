# Adam with bias-corrected moments

For a gradient vector $g_t$ at step $t\ge1$, start at $m_0=v_0=0$, fix $0\le\beta_1,\beta_2<1$ and $\epsilon>0$, and use learning rate $\alpha>0$. Adam updates each coordinate by

$$m_t=\beta_1m_{t-1}+(1-\beta_1)g_t,\qquad v_t=\beta_2v_{t-1}+(1-\beta_2)g_t^2,$$

$$\widehat m_t=m_t/(1-\beta_1^t),\quad \widehat v_t=v_t/(1-\beta_2^t),\quad \theta_t=\theta_{t-1}-\alpha\,\widehat m_t/(\sqrt{\widehat v_t}+\epsilon).$$

The second moment is uncentered; the stabilizer is outside the square root. The correction factors undo the zero initialization of the moving averages for a constant gradient. This update rule is not a convergence theorem.

## Background

- [Minibatch SGD with momentum](minibatch-sgd-with-momentum.md)

## Sources

- Kingma and Ba, [*Adam: A Method for Stochastic Optimization*](https://arxiv.org/abs/1412.6980) (ICLR 2015), §2, algorithm 1.
