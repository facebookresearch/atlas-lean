# Suffix-cell property of chaos game representation

**Construction (CGR and universal sequence map).** Let the alphabet have $M$ symbols and set $D = \lceil \log_2 M \rceil$. Assign each symbol a distinct vertex $U \in \{0,1\}^D$ of the unit hypercube. For a sequence $s_1 s_2 \dots s_N$ with vertex codes $U(i) = (U_1(i), \dots, U_D(i))$, the forward map is
$$u^f_j(i) = \tfrac12\, u^f_j(i-1) + \tfrac12\, U_j(i), \qquad i = 1, \dots, N,\ j = 1, \dots, D,$$
from a seed $u^f(0) \in [0,1]^D$, and the backward map $u^b_j(i) = \tfrac12 u^b_j(i+1) + \tfrac12 U_j(i)$ iterates from the end. For DNA ($M = 4$, $D = 2$) the forward map is the chaos game representation in the unit square. The scale-independent seeding uses the mirror sequence, $u^f_j(0) = u^b_j(2)$ and $u^b_j(N+1) = u^f_j(N-1)$.

**Proposition.** Unrolling the recursion,
$$u^f_j(i) = \sum_{k=1}^{i} 2^{-k}\, U_j(i-k+1) + 2^{-i}\, u^f_j(0).$$
Consequently, for every $k \le i$:
1. the first $k$ binary digits of $u^f_j(i)$ are $U_j(i), U_j(i-1), \dots, U_j(i-k+1)$, up to the dyadic-boundary ambiguity;
2. the point $u^f(i)$ lies in the dyadic subcube of side $2^{-k}$ indexed by the last $k$ symbols $s_{i-k+1} \dots s_i$, and two positions whose preceding $k$ symbols coincide lie within distance $2^{-k}\sqrt D$ of each other, whatever precedes them;
3. counting points of the map in the $M^k$ dyadic cells of side $2^{-k}$ (when $M = 2^D$) recovers exactly the frequency table of $k$-mers, that is, an order-$(k-1)$ Markov transition table, and finer cells resolve longer memories.

Symmetrically, the backward map places a position by its following symbols, so a shared motif of length $k$ in two sequences produces forward and backward coordinates that are close to the same degree regardless of where the motif occurs.

## Expansion

Each iteration halves the distance to the vertex of the current symbol, which in binary prepends the bit $U_j(i)$ to the expansion of $u^f_j(i-1)$ and shifts the older digits right; the seed's influence decays as $2^{-i}$. This makes CGR a lossless, bijective encoding of a sequence as a point of the hypercube and turns $k$-mer counting into box counting at scale $2^{-k}$, so non-integer (fractal) resolutions interpolate between Markov orders. Seeding at the center $1/2$ creates artificial density at the dyadic points $1/4, 3/4, 1/8, \dots$ near the sequence start; seeding with the mirror-image coordinate removes this artifact. Kernel densities built from nested cells weighted across scales give scale-independent motif distributions.

## Sources

- J. S. Almeida, S. Vinga, "Computing distribution of scale independent motifs in biological sequences", Algorithms for Molecular Biology 1 (2006) 18, Results, Equations 1-2, <https://doi.org/10.1186/1748-7188-1-18>, PMCID PMC1630425.
- H. J. Jeffrey, "Chaos game representation of gene structure", Nucleic Acids Research 18(8) (1990) 2163-2170, <https://doi.org/10.1093/nar/18.8.2163>.
