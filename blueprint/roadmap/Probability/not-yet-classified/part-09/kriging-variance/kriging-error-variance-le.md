# Optimality of the ordinary kriging weights

Let $K$ be a positive semidefinite matrix, $c$ a vector and $\sigma$ a real number, and write $V(u) = \sigma + u^{\mathsf T}Ku - 2u^{\mathsf T}c$ for the kriging prediction-error variance of weights $u$. If weights $w$ with $\sum_i w_i = 1$ satisfy the stationarity condition $Kw + \lambda\mathbf 1 = c$ for some $\lambda$, then $V(w) \le V(v)$ for all weights $v$ with $\sum_i v_i = 1$.
