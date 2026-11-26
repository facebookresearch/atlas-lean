# Attention outputs lie in the convex hull of the values

Let $X$ be $n$ token vectors in $\mathbb{R}^d$, $W_Q, W_K$ query and key matrices of size $d \times d_k$ with key dimension $d_k \ge 1$, and $W_V$ a value matrix of size $d \times d_v$. Then for every token $i$, the softmax self-attention output row $i$ lies in the convex hull of the value rows $X_j W_V$, $j < n$.
