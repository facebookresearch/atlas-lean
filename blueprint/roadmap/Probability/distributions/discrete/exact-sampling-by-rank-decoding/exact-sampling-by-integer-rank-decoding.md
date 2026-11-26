# Exact sampling by integer rank decoding in a binary probability tree

Let $d \in \mathbb{N}$ and let $m$ assign a natural-number mass to every binary string of length at most $d$ such that $m(w) = m(w0) + m(w1)$ for every $w$ of length less than $d$. The *rank decoder* maps a rank $\rho < m(\varepsilon)$ (where $\varepsilon$ is the empty string) to a leaf of length $d$ by walking down from the root: at node $w$ with residual rank $\rho$, go to $w0$ if $\rho < m(w0)$ and otherwise to $w1$ with residual rank $\rho - m(w0)$. Then every leaf $w$ of length $d$ is the output of exactly $m(w)$ ranks; hence decoding a uniformly random rank in $\{0, \dots, m(\varepsilon) - 1\}$ outputs $w$ with probability $m(w)/m(\varepsilon)$, and when $m(\varepsilon) = 2^k$ the decoder applied to $k$ fair bits samples this distribution exactly. Every valid rank reaches a leaf of positive mass, and the decoder makes $d$ adaptive mass queries.

## Proof sketch

By induction on the depth, the set of ranks sent to the subtree of $w$ is an interval of length $m(w)$: the root receives $[0, m(\varepsilon))$, and splitting an interval of length $m(w)$ at $m(w0)$ sends intervals of lengths $m(w0)$ and $m(w1)$ to the children. The leaf statement and the uniform-rank law follow, and $k$ fair bits encode a uniform rank below $2^k$.

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
