# Minimal per-flow regulators

Let $\Pi$ be a regulation operator in the sense of [Pi-regularity](pi-regularity.md) and $(A, L)$ a single-flow packet sequence. Define $D_1 = A_1$ and

$$
D_n = \max\{A_n,\ D_{n-1},\ \Pi(D, L)_n\} \qquad (n \ge 2),
$$

which is well defined because $\Pi(D, L)_n$ depends only on $D_1, \dots, D_{n-1}$. The FIFO system mapping $(A, L)$ to $(D, L)$, the *minimal $\Pi$-regulator*, satisfies:

1. it is a $\Pi$-regulator for the flow;
2. (minimality) every $\Pi$-regulator that maps $(A, L)$ to some $(D', L)$ has $D'_n \ge D_n$ for all $n$;
3. $(A, L)$ is $\Pi$-regular if and only if $D = A$.

For the arrival curve operator of an unbounded $\sigma$ with $\sigma^\downarrow(L_n) = 0$ for every $n$ it is the packetized greedy shaper; for a leaky bucket it gives the max-plus equation of the leaky bucket shaper.

## Depends on

- [Pi-regularity](pi-regularity.md)

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>; section, theorem and equation numbers are those of the arXiv version, Section IV.A, Theorem 2, equation (44), with its proof in the appendix, and Section IV.C (the packetized greedy shaper and the leaky bucket shaper).
