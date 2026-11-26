# Plane-sweep filtering of dominated alignment segments

**Problem.** Let the candidate mappings of a query be $n$ weighted intervals $s = ([b_s, e_s], w_s)$ on the query coordinate, weighted by alignment score. A segment is *redundant* iff at every position $x \in [b_s, e_s]$ it is covered by some segment of strictly higher score; it is *good* otherwise. Scores need not be distinct. The task is to output all good segments.

**Order.** Compare segments by score, breaking ties by start position: $s \prec s'$ iff $w_s < w_{s'}$, or $w_s = w_{s'}$ and $b_s < b_{s'}$.

**Algorithm.** Sweep a vertical line over the $2n$ endpoints in coordinate order, maintaining in a height-balanced binary search tree $\mathcal L$ (keyed by $\prec$) the segments that intersect the line. At each endpoint, insert the starting or delete the ending segment, then mark as good the segments of maximum score currently in $\mathcal L$ by walking from the maximum through its predecessors while the score stays maximal, stopping early as soon as an already-marked segment is reached.

**Statements.**

1. A segment is good iff at some endpoint position it has the maximum score among the segments intersecting the sweep line there, so evaluating $\mathcal L$ only at the $2n$ endpoints suffices.
2. With the tie-breaking order and the early-stopping rule, the algorithm runs in $O(n \log n)$ time; insert and delete cost $O(\log n)$ and the marking walk costs $O(\log n)$ per newly marked segment plus $O(\log n)$ per endpoint.
3. $\Omega(n \log n)$ time is necessary for this filtering problem in the worst case (proved in the source), so the algorithm is asymptotically optimal.

For genome-to-genome maps the filter is applied twice, once along the query and once along the reference; mappings passing both form a one-to-one (orthology-like) map, while split-read mapping uses the query-side filter only.

## Expansion

For statement 1: the set of segments covering a point changes only at endpoints, so the maximum score over the line is piecewise constant between consecutive endpoints and attained on an endpoint's neighbourhood; a segment not dominated at some point is maximal on the elementary interval containing that point, hence at one of its bounding endpoints. The early stop relies on a property established in the source: when the walk reaches a segment already marked good, every remaining maximum-score segment below it in $\mathcal L$ has also been marked already, so continuing would only repeat work; the tie-break by start position is what makes this property, and with it the $O(n \log n)$ bound, hold. This filter is the special case $K = 1$ of the BLAST-style criterion that discards a match covered at every position by at least $K$ higher-scoring matches; unlike an interval tree over all segments, the sweep tree holds only the segments crossing the current line, usually far fewer than $n$. The design follows the Shamos–Hoey plane sweep for detecting intersecting segments.

## Sources

- C. Jain, S. Koren, A. Dilthey, A. M. Phillippy, S. Aluru, "A fast adaptive algorithm for computing whole-genome homology maps", Bioinformatics (2018), Section 2.2 ("A geometric algorithm for filtering alignments": problem formulation, Shamos–Hoey algorithm, proposed algorithm, $O(n \log n)$ upper and $\Omega(n \log n)$ lower bounds), Sections 2.3–2.4, <https://doi.org/10.1093/bioinformatics/bty597> (PMC6129286).
