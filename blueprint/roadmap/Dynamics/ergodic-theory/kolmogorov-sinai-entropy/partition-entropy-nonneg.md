# Entropy of a partition is nonnegative

Let $\mu$ be a probability measure on $X$ and $\xi = (C_i)_{i \in I}$ a family of subsets of $X$ indexed by a
finite set $I$. Then its [entropy](partition-entropy.md) is nonnegative,

$$H_\mu(\xi) = -\sum_{i \in I} \mu(C_i) \log \mu(C_i) \ge 0,$$

since every $\mu(C_i)$ lies in $[0, 1]$ and $-t \log t \ge 0$ there.
