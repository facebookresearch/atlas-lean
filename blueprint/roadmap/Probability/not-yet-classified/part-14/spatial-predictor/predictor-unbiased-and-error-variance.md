# Unbiased linear predictor and its error variance

Let $X$ and $Y_1, \dots, Y_n$ be square-integrable random variables on a probability space with $\mathbb{E}[Y_i] = \mathbb{E}[X]$ for all $i$, and let weights $w$ satisfy $\sum_i w_i = 1$. Then the predictor $\sum_i w_i Y_i$ has mean $\mathbb{E}[X]$, and

$$\operatorname{Var}\Big(X - \sum_i w_i Y_i\Big) = \operatorname{Var}(X) - 2\, w^\top c + w^\top K w,$$

where $c_i = \operatorname{Cov}(X, Y_i)$ and $K_{ij} = \operatorname{Cov}(Y_i, Y_j)$.
