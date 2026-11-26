# Block at a binary index fixes the last variables

Let $n$ and $k$ be natural numbers, $F$ a Boolean function on $\{0,1\}^{n+k}$ and $y \in \{0,1\}^k$, where the binary index of $y \in \{0,1\}^k$ is $\iota(y) = \sum_{j < k} y_j 2^j$, with $y_j \in \{0, 1\}$ and for a Boolean function $F$ on $\{0,1\}^{n+k}$ and a natural number $i$, the block $F_i$ is the Boolean function $x \mapsto F(x_0, \dots, x_{n-1}, \beta_0(i), \dots, \beta_{k-1}(i))$ on $\{0,1\}^n$, where $\beta_j(i)$ is bit $j$ of $i$. Then $F_{\iota(y)}$ is the function $x \mapsto F(x_0, \dots, x_{n-1}, y_0, \dots, y_{k-1})$.
