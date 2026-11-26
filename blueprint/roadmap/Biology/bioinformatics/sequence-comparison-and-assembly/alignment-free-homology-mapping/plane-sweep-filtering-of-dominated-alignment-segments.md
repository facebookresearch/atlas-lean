# Plane-sweep filtering of dominated alignment segments

**Problem.** Let the candidate mappings of a query be $n$ weighted intervals $s = ([b_s, e_s], w_s)$ with integer endpoints $b_s \le e_s$ on the query coordinate, weighted by alignment score; segment $s$ covers the integer positions $x$ with $b_s \le x \le e_s$. A segment is *redundant* iff at every position $x \in [b_s, e_s]$ it is covered by some segment of strictly higher score; it is *good* otherwise. Scores need not be distinct. The task is to output all good segments.

**Order.** Compare segments by score, breaking ties by start position: $s \prec s'$ iff $w_s < w_{s'}$, or $w_s = w_{s'}$ and $b_s < b_{s'}$.

**Events.** Treat segment $s$ as the half-open interval $[b_s, e_s + 1)$: it has a start event at $b_s$ and an end event at $e_s + 1$. Let $x_1 < x_2 < \dots < x_k$ ($k \le 2n$) be the distinct event coordinates. On each range $[x_j, x_{j+1})$ the set of segments covering a position does not change; call it the active set $A_j$.

**Algorithm.** Sweep the event coordinates in increasing order, maintaining in a height-balanced binary search tree $\mathcal L$ (keyed by $\prec$) the active segments. At each coordinate $x_j$, first process all events at $x_j$ together (delete every segment ending there and insert every segment starting there), so that $\mathcal L$ holds $A_j$. Then, if $\mathcal L$ is nonempty and $j < k$, mark as good the segments of maximum score in $\mathcal L$ by walking from the maximum through its predecessors while the score stays maximal, stopping early as soon as an already-marked segment is reached.

**Statements.**

1. A segment $s$ is good iff for some $j$ with $[x_j, x_{j+1}) \cap [b_s, e_s + 1) \ne \varnothing$ it has the maximum score in $A_j$; so evaluating $\mathcal L$ once per nonempty constant-active range, after all events at its left end are processed, suffices.
2. With the tie-breaking order and the early-stopping rule, the algorithm runs in $O(n \log n)$ time; insert and delete cost $O(\log n)$ and the marking walk costs $O(\log n)$ per newly marked segment plus $O(\log n)$ per event coordinate.
3. $\Omega(n \log n)$ time is necessary for this filtering problem in the worst case (proved in the source), so the algorithm is asymptotically optimal.

For genome-to-genome maps the filter is applied twice, once along the query and once along the reference; mappings passing both form a one-to-one (orthology-like) map, while split-read mapping uses the query-side filter only.

## Expansion

For statement 1: a position $x$ with $b_s \le x \le e_s$ lies in exactly one range $[x_j, x_{j+1})$, and that range lies inside $[b_s, e_s + 1)$ because $b_s$ and $e_s + 1$ are event coordinates; the segments covering $x$ are exactly $A_j$. So $s$ fails to be dominated at $x$ iff it has the maximum score in $A_j$, and the ranges meeting $[b_s, e_s + 1)$ are those contained in it. Coincident events must be processed together: if a segment ending at $e$ and one starting at $e + 1$ were handled one at a time, the tree would briefly hold a set that covers no position. Testing only at input endpoints is not enough: with integer segments $[1, 9]$ of score $1$ and $[0, 3]$, $[7, 10]$ of score $2$, the first segment is the only one covering positions $4, \dots, 6$, so it is good, yet at every one of the endpoints $0, 1, 3, 7, 9, 10$ it is covered by a segment of score $2$ or absent. The early stop relies on a property established in the source: when the walk reaches a segment already marked good, every remaining maximum-score segment below it in $\mathcal L$ has also been marked already, so continuing would only repeat work; the tie-break by start position is what makes this property, and with it the $O(n \log n)$ bound, hold. This filter is the special case $K = 1$ of the BLAST-style criterion that discards a match covered at every position by at least $K$ higher-scoring matches; unlike an interval tree over all segments, the sweep tree holds only the segments crossing the current line, usually far fewer than $n$. The design follows the Shamos–Hoey plane sweep for detecting intersecting segments.

## Sources

- C. Jain, S. Koren, A. Dilthey, A. M. Phillippy, S. Aluru, "A fast adaptive algorithm for computing whole-genome homology maps", Bioinformatics (2018), Section 2.2 ("A geometric algorithm for filtering alignments": problem formulation, Shamos–Hoey algorithm, proposed algorithm, $O(n \log n)$ upper and $\Omega(n \log n)$ lower bounds), Sections 2.3–2.4, <https://doi.org/10.1093/bioinformatics/bty597> (PMC6129286).
