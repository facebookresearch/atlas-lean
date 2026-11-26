# Quantum search with an unknown number of marked items (BBHT)

Let $x \in \{0,1\}^N$ have $t \ge 1$ marked positions, $t$ unknown. Running Grover's iteration a number of times chosen uniformly from $\{0, \dots, M - 1\}$ with $M \ge \sqrt{N/t}$ (suitably scaled) and measuring finds a marked item with probability at least $1/4$. Iterating with geometrically increasing $M$ gives an algorithm that finds a marked item with $O(\sqrt{N/t})$ expected queries, and a fixed-budget algorithm with $O(\sqrt N)$ queries computes $\mathrm{OR}_N$ with error at most $1/3$.

## Proof sketch

After $j$ iterations the success probability is $\sin^2((2j+1)\theta)$ with $\sin^2\theta = t/N$. Averaging over a uniform $j < M$ gives $\frac12 - \frac{\sin(4M\theta)}{4M\sin(2\theta)}$, which is at least $1/4$ once $M \ge 1/\sin(2\theta)$.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)
- [Exact success probability of Grover search](../grover-s-algorithm/marked-probability-grover-iterate-unifor.md)

## Proof depends on

- [Exact success probability of Grover search](../grover-s-algorithm/marked-probability-grover-iterate-unifor.md)

## Sources

- M. Boyer, G. Brassard, P. Høyer and A. Tapp, "Tight Bounds on Quantum Searching", Fortschritte der Physik 46(4-5), 1998.
- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
