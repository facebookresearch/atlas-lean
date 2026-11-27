# Re-shaping does not increase backlog or delay bounds

Assume a flow constrained by a good [arrival curve](arrival-curves.md) $\alpha$ is input to systems $S_1$ and $S_2$ in sequence, offering [service curves](service-curves.md) $\beta_1$ and $\beta_2$, and a [greedy shaper](greedy-shapers.md) with a good shaping curve $\sigma \ge \alpha$ is inserted between them. Then the delay bounds computed for the system with the shaper equal those computed without it, $h(\alpha, \beta_1 \otimes \sigma \otimes \beta_2) = h(\alpha, \beta_1 \otimes \beta_2)$, and so do the backlog bounds when $\alpha$ is finite, $v(\alpha, \beta_1 \otimes \sigma \otimes \beta_2) = v(\alpha, \beta_1 \otimes \beta_2)$. More generally, for good $\alpha \le \sigma$ and any $\beta$, $h(\alpha, \sigma \otimes \beta) = h(\alpha, \beta)$, and $v(\alpha, \sigma \otimes \beta) = v(\alpha, \beta)$ when $\alpha$ is finite. Greedy shapers thus come for free in worst-case delay, while they reduce the burstiness admitted into the next node.

## Depends on

- [Greedy shapers](greedy-shapers.md)
- [Sub-additive closure](min-plus-algebra/sub-additive-closure.md): the good curves.
- [Service curves](service-curves.md)
- [Vertical and horizontal deviations](min-plus-algebra/vertical-and-horizontal-deviations.md)

## Proof depends on

- [Input-output characterization of greedy shapers](input-output-characterization-of-greedy-shapers.md): the shaper offers the service curve $\sigma$.
- [Concatenation of service curves](concatenation-of-service-curves.md)
- [The backlog bound](the-backlog-bound.md)
- [The delay bound](the-delay-bound.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.5.3, Theorem 1.5.2 and Lemma 1.5.2 with their proofs.
