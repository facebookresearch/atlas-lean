# Impact of a packetizer

Consider a first-in-first-out, lossless bit-by-bit system with $L$-packetized input $R$ and output $R^*$, where packet $i$ arrives at time $T_i$ and $R(t) = L(i)$ for $T_i \le t < T_{i+1}$, as in the source's proof, followed by an [$L$-packetizer](packetizers.md) that produces the final output $R' = P^L(R^*)$; the combined system maps $R$ to $R'$. Then:

1. the per-packet delay of the combined system, $\sup_i (T'_i - T_i)$, where $T'_i = \inf\{t : R'(t) \ge L(i)\}$ is the departure time of packet $i$, equals the maximum virtual delay of the bit-by-bit system;
2. the maximum backlogs satisfy $B^* \le B' \le B^* + l_{\max}$, for $B^*$ of the bit-by-bit system and $B'$ of the combined one;
3. if the bit-by-bit system offers the flow a [service curve](../service-curves.md) $\beta$, the combined system offers the service curve $\beta'(t) = [\beta(t) - l_{\max}]^+$;
4. if a flow $S$ has [arrival curve](../arrival-curves.md) $\alpha$, then $P^L(S)$ has arrival curve $\alpha(t) + l_{\max}\mathbf 1_{\{t > 0\}}$.

So a packetizer does not increase the per-packet delay at a node, but it weakens a rate-latency service curve of rate $R$ by an extra latency $l_{\max}/R$.

## Depends on

- [Packetizers](packetizers.md)
- [Service curves](../service-curves.md)
- [Arrival curves](../arrival-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.7.2, Definition 1.7.5 (per-packet delay) and Theorem 1.7.1 with its proof; the theorem also states that a maximum service curve of the bit-by-bit system carries over, which this page omits.
