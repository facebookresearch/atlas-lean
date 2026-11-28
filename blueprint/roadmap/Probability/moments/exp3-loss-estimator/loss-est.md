# EXP3 importance-weighted loss estimate

The EXP3 importance-weighted loss estimator. Let $n \in \mathbb{N}$, with arms $\{0, \dots, n-1\}$, let $p = (p_i)$ be any real vector and $l = (l_i)$ a real loss vector. When arm $j$ is sampled, the estimate of the loss of arm $i$ is

$$\hat{l}_{j,i} = \begin{cases} l_i / p_i & \text{if } j = i, \\ 0 & \text{if } j \ne i, \end{cases}$$

with the convention $x / 0 = 0$, so $\hat{l}_{i,i} = 0$ when $p_i = 0$.

In EXP3, $p$ is the probability vector from which the played arm is sampled, and then $\hat l_{j,i}$ is the importance-weighted estimate of $l_i$. The definition itself accepts any real vector, such as $p = (-1, 2)$, which is not a sampling distribution.
