# Blocks of a monotone function increase with the index bits

Let $n$ and $k$ be natural numbers and let $F$ be a monotone Boolean function on $\{0,1\}^{n+k}$ (coordinatewise order, $0 < 1$); for a Boolean function $F$ on $\{0,1\}^{n+k}$ and a natural number $i$, the block $F_i$ is the Boolean function $x \mapsto F(x_0, \dots, x_{n-1}, \beta_0(i), \dots, \beta_{k-1}(i))$ on $\{0,1\}^n$, where $\beta_j(i)$ is bit $j$ of $i$. Let $i$ and $i'$ be natural numbers such that for every $m < k$, if bit $m$ of $i$ is $1$ then bit $m$ of $i'$ is $1$. Then $F_i \le F_{i'}$ pointwise.
