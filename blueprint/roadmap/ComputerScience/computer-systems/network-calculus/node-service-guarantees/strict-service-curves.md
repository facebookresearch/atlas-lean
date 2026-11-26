# Strict service curves

A system $S$ offers a *strict service curve* $\beta$ to a flow, where $\beta$ is a wide-sense increasing function with $\beta(0) = 0$, if during any backlogged period of duration $u$, an interval throughout which the flow has data in the system, the output of the flow is at least $\beta(u)$. A generalized processor sharing node with allocated rate $r$ offers the strict service curve $t \mapsto rt$; a greedy shaper offers its shaping curve as a [service curve](../service-curves.md) but in general not as a strict one.

## Depends on

- [Service curves](../service-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.3.2, Definition 1.3.2 and the paragraphs after it.
