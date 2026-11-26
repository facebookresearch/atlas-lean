# Sequence-specific minimizers

A $(w, k)$ minimizer samples, from every window of $w$ consecutive $k$-mers of a sequence, the smallest $k$-mer under a fixed order, so that any two sequences sharing a substring of length $w + k - 1$ sample a common $k$-mer. Its density (fraction of positions sampled) is at least $1/w$ and is $2/(w+1)$ for a random order on a random sequence. For a fixed sequence such as a reference genome, the order can be tuned to that sequence; charged-context energy and polar sets give provable density bounds for such tuned orders.

- [Charged contexts and the energy of a random minimizer](charged-contexts-and-the-energy-of-a-random-minimizer.md)
- [Polar sets and the link-energy density bound](polar-sets-and-the-link-energy-density-bound.md)
