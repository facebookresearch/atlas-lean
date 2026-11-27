# Discrete distribution generating (DDG) tree

Let $\alpha$ be a countable set of outcomes. A *discrete distribution generating tree* (DDG tree) over $\alpha$ is a map $T$ from finite binary strings to $\alpha \cup \{\bot\}$ that is absorbing: if $T(w) = a \in \alpha$ then $T(wu) = a$ for every string $u$. It is a possibly infinite binary tree whose leaves carry outcomes; $T(w) = \bot$ means that the walk along $w$ is still at an internal node.

Run $T$ on an infinite sequence of independent coin flips $b_1 b_2 \dots$, each equal to $1$ with probability $\rho \in [0,1]$ (fair bits when $\rho = 1/2$). The stopping time is $\tau = \min\{n : T(b_1 \cdots b_n) \ne \bot\} \in \mathbb{N} \cup \{\infty\}$, and on $\{\tau < \infty\}$ the output is $T(b_1 \cdots b_\tau)$. The *output law* is $q_T(a) = \Pr[\tau < \infty,\ \text{output} = a] = \lim_{n} \Pr[T(b_1\cdots b_n) = a]$, and $T$ *generates* a probability distribution $p$ on $\alpha$ if $q_T = p$. Given costs $w_0, w_1, \dots \ge 0$, where reading flip number $n+1$ costs $w_n$, the *expected cost* is $\sum_{n \ge 0} w_n \Pr[\tau > n] \in [0, \infty]$; with unit costs it is the *expected number of flips* $\mathbb{E}[\tau] = \sum_{n \ge 0} \Pr[\tau > n]$.

## Depends on

- [Uniform distribution on a finite type](../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- Donald E. Knuth and Andrew C. Yao, "The Complexity of Nonuniform Random Number Generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
