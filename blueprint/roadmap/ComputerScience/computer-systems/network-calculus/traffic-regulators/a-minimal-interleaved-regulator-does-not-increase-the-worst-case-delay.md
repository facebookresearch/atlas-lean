# A minimal interleaved regulator does not increase the worst-case delay

Let a packet sequence $(A, L, F)$, as in [minimal interleaved regulators](minimal-interleaved-regulators.md), with real packet dates and in which every flow $f$ is $\Pi^f$-regular enter a system $S$ that is first in, first out for the whole sequence, with output $(D, L, F)$, and feed that output to the [minimal interleaved regulator](minimal-interleaved-regulators.md) with the operators $\Pi^f$, with output $(E, L, F)$. Then

$$
\sup_n (E_n - A_n) = \sup_n (D_n - A_n) :
$$

the worst-case delay of the combination, over all packets, is that of $S$ alone. This is the reason regulators shared by several flows, as in time-sensitive networking, avoid burstiness cascades without adding to worst-case delay bounds computed for FIFO systems.

## Depends on

- [Minimal interleaved regulators](minimal-interleaved-regulators.md)

## Proof depends on

- [A minimal regulator does not increase the worst-case delay](a-minimal-regulator-does-not-increase-the-worst-case-delay.md): the same comparison with a damper of parameter the worst-case delay of $S$.

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>; section, theorem and equation numbers are those of the arXiv version, Section V.B, Theorem 5, equation (50), with its proof.
