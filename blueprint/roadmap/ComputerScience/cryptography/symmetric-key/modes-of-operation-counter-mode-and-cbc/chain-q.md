# CBC chain as an oracle algorithm

Let $X$ be a type with an addition (no other structure is required). For an initial value $\mathrm{iv}$ and a message $m \in X^n$, the oracle computation with queries and answers in $X$ is defined recursively: for $n = 0$ it returns the empty vector; for $n + 1$ it queries $\mathrm{iv} + m_1$, and on answer $c$ it runs the same computation from $c$ on the remaining blocks $m_2, \dots, m_{n+1}$ and returns $c$ followed by their outputs. No property of the oracle is assumed; run against a block cipher's permutation it computes the CBC chain.
