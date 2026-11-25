# Message complexity of Hirschberg–Sinclair leader election

On a bidirectional ring of $n$ processes with distinct identifiers, the Hirschberg–Sinclair algorithm, in which each candidate probes in both directions to distances $1, 2, 4, \dots$ and survives a phase only if no larger identifier lies within the probed distance, elects the process with the maximum identifier using $O(n \log n)$ messages.

## Expansion

This page becomes ready once these prerequisites are stated:

- Bidirectional ring with reliable message execution (statement prerequisite; not yet stated)

## Sources

- D. S. Hirschberg and J. B. Sinclair, "Decentralized extrema-finding in circular configurations of processors", *Communications of the ACM* 23(11):627–628, 1980
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
