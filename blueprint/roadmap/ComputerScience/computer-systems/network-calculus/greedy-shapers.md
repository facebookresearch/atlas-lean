# Greedy shapers

A *shaper* with shaping curve $\sigma$ is a bit-processing system that forces its output to have $\sigma$ as an [arrival curve](arrival-curves.md). A *greedy shaper* with shaping curve $\sigma$ is a shaper that delays the input bits in a buffer whenever sending a bit would violate the constraint $\sigma$, and outputs them as soon as possible otherwise. A *policer* with curve $\sigma$ instead counts the bits arriving on an input flow and decides which of them conform with the arrival curve $\sigma$.

## Depends on

- [Arrival curves](arrival-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.5.1.
