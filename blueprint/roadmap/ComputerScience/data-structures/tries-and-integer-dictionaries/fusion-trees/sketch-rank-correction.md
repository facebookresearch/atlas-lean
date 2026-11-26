# Recovering the rank of an arbitrary query from sketch ranks

Let $x_1 < \dots < x_k$ be stored keys and $q$ any query, and let $t$ be the inclusive rank of $\mathrm{sketch}(q)$ among the stored sketches. Let $x$ be the neighbour among $x_{t}, x_{t+1}$ (those that exist) whose exclusive or with $q$ is smaller. If $x = q$, the inclusive rank of $q$ is $t$. Otherwise let $p$ be the most significant bit where $q$ and $x$ differ. Let $e$ be the word that agrees with $q$ above $p$, has bit $p$ equal to $1 - q_p$ (the common value of bit $p$ of all stored keys sharing $q$'s prefix above $p$), and below $p$ has all ones if $q_p = 1$ and all zeros if $q_p = 0$. Then the inclusive rank of $q$ among the stored keys equals the inclusive rank of $\mathrm{sketch}(e)$ among the stored sketches if $q_p = 1$, and the number of stored sketches strictly below $\mathrm{sketch}(e)$ if $q_p = 0$. Thus two sketch ranks and one most-significant-bit computation suffice to rank an arbitrary query.

## Proof sketch

The neighbour chosen by exclusive or shares the longest prefix with $q$ among all stored keys. All stored keys sharing $q$'s prefix above $p$ form a contiguous block, and $q$ lies just after this block if $q_p = 1$ or just before it if $q_p = 0$. The word $e$ is the largest (respectively smallest) word with that block's prefix, so the keys at most $q$ are the keys at most $e$ (respectively strictly below $e$; $e$ itself may be a stored key), and since $e$ agrees with the block on its prefix and has constant low bits, its sketch ranks equal its true ranks.

## Depends on

- [Significant bits and perfect sketch of a key set](perfect-sketch-of-a-key-set.md)

## Proof depends on

- [Perfect sketches preserve the order of stored keys](sketches-preserve-key-order.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
