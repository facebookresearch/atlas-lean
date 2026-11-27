# Kriging weights are unique

Let $K$ be a positive definite matrix over a finite index set, $c$ a vector and $\sigma$ real. Suppose $w$ satisfies the kriging system $K w + \lambda \mathbf 1 = c$ for some $\lambda$ with $\sum_i w_i = 1$. If $v$ also has $\sum_i v_i = 1$ and the same error variance, $\sigma + v^{\mathsf T} K v - 2 v^{\mathsf T} c = \sigma + w^{\mathsf T} K w - 2 w^{\mathsf T} c$, then $v = w$.
