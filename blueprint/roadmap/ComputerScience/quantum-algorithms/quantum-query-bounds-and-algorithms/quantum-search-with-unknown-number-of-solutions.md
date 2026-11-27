# Quantum search with an unknown number of marked items (BBHT)

Let $x \in \{0,1\}^N$ have $t$ marked positions with $1 \le t < N$, $t$ unknown. Running Grover's iteration a number of times chosen uniformly from $\{0, \dots, M - 1\}$ and measuring finds a marked item with probability exactly $\frac12-\frac{\sin(4M\theta)}{4M\sin(2\theta)}$, where $\sin^2\theta=t/N$ and $0<\theta<\pi/2$; this is at least $1/4$ whenever $M\ge1/\sin(2\theta)$ (BBHT, Lemma 2). (When $t=N$ every measurement finds a marked item.) Since $1/\sin(2\theta)\le\sqrt{N/t}$ when $t\le 3N/4$, $M\ge\sqrt{N/t}$ suffices in that range. Iterating with geometrically increasing $M$ (factor $\lambda$ with $1 < \lambda < 4/3$) gives an algorithm that finds a marked item with $O(\sqrt{N/t})$ expected queries when $1 \le t \le 3N/4$ (BBHT, Theorem 3); for $t > 3N/4$ classical sampling succeeds in expected $O(1)$ queries. Stopping after a fixed budget of $O(\sqrt N)$ queries (and answering "no marked item" on timeout) computes $\mathrm{OR}_N$ with error at most $1/3$.

## Proof sketch

After $j$ iterations the success probability is $\sin^2((2j+1)\theta)$ with $\sin^2\theta = t/N$. Averaging over a uniform $j < M$ gives $\frac12 - \frac{\sin(4M\theta)}{4M\sin(2\theta)}$, which is at least $1/4$ once $M \ge 1/\sin(2\theta)$.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)
- [Exact success probability of Grover search](../grover-s-algorithm/marked-probability-grover-iterate-unifor.md)

## Sources

- M. Boyer, G. Brassard, P. Høyer and A. Tapp, "Tight Bounds on Quantum Searching", Fortschritte der Physik 46(4-5), 1998 (arXiv:quant-ph/9605034), Lemma 2 and Theorem 3.
- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
