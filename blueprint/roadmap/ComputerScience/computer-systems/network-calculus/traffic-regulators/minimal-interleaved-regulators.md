# Minimal interleaved regulators

A *packet sequence* $(A, L, F)$ of several flows gives, for each packet $n$, its date $A_n$, its length $L_n$ and its flow $F_n$, numbered chronologically across all flows, $A_n \le A_{n+1}$ for every $n$, with a fixed numbering of simultaneous packets, and with finitely many flow labels and infinitely many packets of each flow, as in Le Boudec's model, so that every single-flow subsequence is an infinite sequence on which the operators are defined (by causality, $\Pi^f(D^f, L^f)_j$ depends only on its first $j$ terms); $I(n)$ is the index of packet $n$ within its flow, and $(A^f, L^f)$ is the single-flow sequence of flow $f$. With one regulation operator $\Pi^f$ per flow, in the sense of [Pi-regularity](pi-regularity.md), an *interleaved regulator* is a system that is first in, first out for the whole sequence and whose output makes every flow $f$ $\Pi^f$-regular. Define $D_1 = A_1$ and

$$
D_n = \max\{A_n,\ D_{n-1},\ \Pi^{F_n}(D^{F_n}, L^{F_n})_{I(n)}\} \qquad (n \ge 2).
$$

The FIFO system mapping $(A, L, F)$ to $(D, L, F)$, the *minimal interleaved regulator*, is an interleaved regulator; every interleaved regulator mapping $(A, L, F)$ to some $(D', L, F)$ has $D' \ge D$; and every flow of $(A, L, F)$ is $\Pi^f$-regular if and only if $D = A$. It can be implemented with a single FIFO queue: the packet at its head is released at the earliest time its own flow's constraint allows, and the others wait behind it.

## Depends on

- [Pi-regularity](pi-regularity.md)

## Proof depends on

- [Minimal per-flow regulators](minimal-per-flow-regulators.md)

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>; section, theorem and equation numbers are those of the arXiv version, Section V.A, Theorem 4, equation (49), with its proof in the appendix and the head-of-line implementation described after it.
