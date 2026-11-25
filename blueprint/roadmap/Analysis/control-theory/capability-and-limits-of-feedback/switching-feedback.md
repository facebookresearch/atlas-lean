# Switching feedback from a nearest-neighbor estimate

Fix a threshold $\varepsilon>0$ and a bounded real reference sequence
$(y_t^*)_{t\ge 0}$ in advance. The feedback is a sequence of maps from
real observation histories to real inputs. Set $u_0=0$. For $t\ge 1$, use
$y_0,\ldots,y_t$ and the controls $u_0,\ldots,u_{t-1}$ already computed
from their respective prefixes. Let $i_t$ and $\widehat f_t(y_t)$ be the
nearest-neighbor index and estimate. Write

$$
d_t=|y_t-y_{i_t}|,\qquad
\underline b_t=\min_{0\le j\le t}y_j,\qquad
\overline b_t=\max_{0\le j\le t}y_j.
$$

Define the next input by

$$
u_t=-\widehat f_t(y_t)+
\begin{cases}
\dfrac{\underline b_t+\overline b_t}{2} & \text{if }d_t>\varepsilon,\\
y_{t+1}^* & \text{if }d_t\le\varepsilon.
\end{cases}
$$

In the second case $y_{t+1}^*$ is a prescribed reference value, not the
unobserved output $y_{t+1}$. The recursion therefore assigns an input to
every history using only the observations through that time. The choice
$u_0=0$ initializes the recursion before any past transition is available.

## Depends on

- [Nearest-neighbor estimate from past transitions](nearest-neighbor-estimate.md)

## Sources

- L. Guo, [*Exploring the capability and limits of the feedback mechanism*](https://arxiv.org/pdf/math/0305011v1),
  Proc. ICM 2002, Vol. III, arXiv:math/0305011v1, Remark 4.1, pp. 6–7. The
  switch is the one in the source for $t\ge1$; the initialization makes the
  law explicit at time $0$.
