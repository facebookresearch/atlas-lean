# A coin of any bias from fair bits with two expected flips

Let $\rho \in [0,1]$ and let $d_0 d_1 d_2 \dots \in \{0,1\}^{\mathbb{N}}$ satisfy $\rho = \sum_{i \ge 0} d_i 2^{-(i+1)}$ (for $\rho = 1$ take all $d_i = 1$). The digit-comparison tree reads fair bits $b_0 b_1 \dots$ and, at the first index $i$ with $b_i \ne d_i$, outputs $d_i$. Then:

1. it outputs $1$ with probability exactly $\rho$;
2. it is still running after $n$ flips with probability exactly $2^{-n}$, so its expected number of fair flips is exactly $2$, independently of $\rho$;
3. if computing the digit $d_n$ (needed only when flip $n+1$ is read) costs $w_n$, the expected total digit cost is $\sum_{n \ge 0} w_n 2^{-n}$, which is finite whenever $w_n$ is bounded by a polynomial in $n$.

## Proof sketch

The output is $1$ exactly when the uniform real $0.b_0b_1\cdots$ lies below $0.d_0d_1\cdots = \rho$, an event of probability $\rho$. The tree has not stopped after $n$ flips exactly when $b_0\cdots b_{n-1} = d_0 \cdots d_{n-1}$, which has probability $2^{-n}$; summing the tails gives $2$. The digit-cost formula is the weighted tail sum, and $\sum_n n^c 2^{-n} < \infty$.

## Depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Proof depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Sources

- L. Devroye, "Non-Uniform Random Variate Generation", Springer, 1986, Chapter XV, Section 1.2 (the Bernoulli($p$) generator that compares random bits with the binary expansion of $p$, exits after $i$ bits with probability $2^{-i}$ and uses exactly $2$ bits on average).
