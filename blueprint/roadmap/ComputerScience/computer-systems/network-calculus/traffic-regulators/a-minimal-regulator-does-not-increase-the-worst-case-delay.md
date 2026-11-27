# A minimal regulator does not increase the worst-case delay

Let a [$\Pi$-regular](pi-regularity.md) flow $(A, L)$ with real packet dates enter a system $S$ that is first in, first out for the flow, with output $(D, L)$, and feed that output to the [minimal $\Pi$-regulator](minimal-per-flow-regulators.md) with the same operator, with output $(E, L)$. Then the worst-case delay through the combination equals the worst-case delay through $S$:

$$
\sup_n (E_n - A_n) = \sup_n (D_n - A_n) .
$$

**Proof.** Let $d = \sup_n (D_n - A_n)$, assumed finite. A damper that delivers packet $n$ at time $A_n + d$ is FIFO for $(D, L)$, and its output $(A + d, L)$ is $\Pi$-regular by homogeneity; so it is a $\Pi$-regulator, and minimality gives $E_n \le A_n + d$. Since $E \ge D$, the reverse inequality holds too.

## Depends on

- [Pi-regularity](pi-regularity.md)
- [Minimal per-flow regulators](minimal-per-flow-regulators.md)

## Sources

- J.-Y. Le Boudec, "A theory of traffic regulators for deterministic networks with application to interleaved regulators", *IEEE/ACM Transactions on Networking* 26(6):2721–2733, 2018; arXiv:1801.08477, <https://arxiv.org/abs/1801.08477>; section, theorem and equation numbers are those of the arXiv version, Section IV.D, Theorem 3, equation (48), with its proof (Figure 2).
